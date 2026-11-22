-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch283_Segment001
-- name    : Polychromatic418967fa_Branch283_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:57:38.25749+00:00
-- url     : https://prove2.me/theorems/21e13eb6-16b5-468d-9db5-aaf46cc4829c
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch283_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_283_segment_001 : allB 181 283 :=
  allB_succ' 104 180 283 (Eq.refl Bool.true) (allA_succ_of_accept 103 180 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 180 283 (Polychromatic418967fa.accept_16_6_4_11_1_1719 102 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 180 283 (accept_3_3 101 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 180 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 180 283 (accept_3_3 98 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 180 283 (Polychromatic418967fa.accept_19_2_9_17_1_626 97 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 180 283 (Polychromatic418967fa.accept_19_1_9_17_1_8039 96 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 180 283 (accept_3_3 95 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 180 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 94 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 180 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 180 283 (accept_3_3 92 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 180 283 (Polychromatic418967fa.accept_22_3_4_19_1_17375 91 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 180 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 90 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 180 283 (accept_3_3 89 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 180 283 (Polychromatic418967fa.accept_16_8_4_11_1_2687 88 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 180 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 87 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 180 283 (accept_3_3 86 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 180 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 84 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 180 283 (accept_3_3 83 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 180 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 82 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 180 283
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 180 283 (accept_3_3 80 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 180 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 180 283 (accept_3_3 77 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 180 283
  (Polychromatic418967fa.accept_16_12_4_11_1_3710 76 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 180 283 (Polychromatic418967fa.accept_14_5_12_3_1_3397 75 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 180 283 (accept_3_3 74 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 180 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 73 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 180 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 180 283 (accept_3_3 71 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 180 283 (Polychromatic418967fa.accept_16_6_4_11_1_1719 70 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 180 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 180 283 (accept_3_3 68 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 180 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 180 283
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 180 283 (accept_3_3 65 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 180 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 180 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 180 283 (accept_3_3 62 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 180 283
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 61 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 180 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 180 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 180 283 (accept_3_3 59 180 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268
  57 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 180 283 (accept_3_3 56
  180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 180 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 180 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 180 283 (accept_3_3 53 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 180 283 (Polychromatic418967fa.accept_17_1_10_11_1_2943 52 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 180 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 180 283 (accept_3_3 50 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 180 283 (Polychromatic418967fa.accept_19_11_9_17_1_8038 49 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 180 283 (Polychromatic418967fa.accept_21_6_12_10_1_2576 48 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 180 283 (accept_3_3 47 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 180 283 (Polychromatic418967fa.accept_19_8_9_17_1_5151 46 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 180 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 180 283 (accept_3_3 44 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 180 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 283 (accept_3_3 41 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 180 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 180 283 (accept_3_3 38 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 283 (accept_3_3 35 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 180 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 180 283
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 180 283 (accept_3_3 32 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 180 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 283 (accept_3_3 29 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 180 283
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 180 283 (accept_3_3 26 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 180 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 283
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 24 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 180 283 (accept_3_3 23 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 180 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 283 (accept_3_3 20 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 283 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 180
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 283
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 283 (accept_3_3 17 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 283 (accept_3_3 14 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 283 (Polychromatic418967fa.accept_19_13_9_17_1_8070 13 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 180 283 (accept_3_3 11 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 180 283 (Polychromatic418967fa.accept_25_10_5_8_1_17374 10 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 180 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 283 (accept_3_3 8 180 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 283
  (Polychromatic418967fa.accept_16_6_4_11_1_1719 6 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 180 283 (accept_3_3 5 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  180 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 180 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 180 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 283 (accept_3_3 2 180 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 179 283 (Eq.refl Bool.true) (allA_of_3_1 105 179 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 178 283 (Eq.refl Bool.true) (allA_succ_of_accept 105 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  105 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 178 283 (accept_3_3
  104 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 178 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 103 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 178 283 (accept_3_3 101 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 178 283 (accept_3_3 98 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 178 283 (accept_3_3 95 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 178 283 (Polychromatic418967fa.accept_17_9_8_11_1_1040 94 178 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 178 283 (accept_3_3 92 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 178 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 90 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 178 283 (accept_3_3 89 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 178 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 178 283 (accept_3_3 86 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 178 283 (accept_3_3 83 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 178 283 (accept_3_3 80 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 178 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 79 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 178 283 (accept_3_3 77 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 178 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 178 283 (accept_3_3 74 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 178 283 (Polychromatic418967fa.accept_19_15_7_17_1_5168 72 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 178 283 (accept_3_3 71 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 178 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 70 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 178 283 (accept_3_3 68 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 178 283 (Polychromatic418967fa.accept_19_10_7_17_1_9496 67 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 178 283 (accept_3_3 65 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 178 283 (accept_3_3 62 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 178 283 (accept_3_3 59 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 178 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 58 178 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 178 283 (accept_3_3 56 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 178 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 178 283 (accept_3_3 53 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 178 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 178 283 (accept_3_3 50 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 178 283 (accept_3_3 47 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 178 283 (accept_3_3 44 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 178 283 (Polychromatic418967fa.accept_17_9_8_11_1_1040 43 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 178 283 (accept_3_3 41 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 178 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 178 283 (accept_3_3 38 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 178 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 283 (accept_3_3 35 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 283 (accept_3_3 32 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 283 (accept_3_3 29 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 283 (accept_3_3 26 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 283 (accept_3_3 23 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 178 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 283 (accept_3_3 20 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 283 (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 283 (accept_3_3 17 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 178
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 283 (accept_3_3 14 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 283 (accept_3_3 11 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 283 (accept_3_3 8 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 283 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 283 (accept_3_3 5 178 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 178 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 283 (accept_3_3 2 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 177 283 (Eq.refl Bool.true) (allA_succ_of_accept 106 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 177 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 177 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 177 283 (accept_3_3 104 177 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 177 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 177 283 (accept_3_3 101 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 177 283 (accept_3_3 98 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 177 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 177 283 (accept_3_3 95 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 177 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 177 283 (accept_3_3 92 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 177 283 (accept_3_3 89 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 177 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 177 283 (accept_3_3 86 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 177 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 177 283 (accept_3_3 83 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 177 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 283 (accept_3_3 80 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 177 283 (accept_3_3 77 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 177 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 283 (accept_3_3 74 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 283
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 177 283 (accept_3_3 71 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 177 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 283 (accept_3_3 68 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 177 283 (accept_3_3 65 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 177 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 283 (accept_3_3 62 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 177 283
  (Polychromatic418967fa.accept_16_12_1_11_1_5958 60 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 177 283 (accept_3_3 59 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 177 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 283 (accept_3_3 56 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 283 (Polychromatic418967fa.accept_7_6_2_3_1_107
  55 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 177 283 (accept_3_3 53 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 177 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 283 (accept_3_3 50 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 283 (Polychromatic418967fa.accept_19_11_6_17_1_9455 49 177
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 177 283 (accept_3_3 47 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 177 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 283 (accept_3_3 44 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 283 (accept_3_3 41 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 283 (accept_3_3 38 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 283 (accept_3_3 35 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 283 (accept_3_3 32 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 283 (accept_3_3 29 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 283 (accept_3_3 26 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 283 (accept_3_3 23 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 283 (accept_3_3 20 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 283 (accept_3_3 17 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 283 (accept_3_3 14 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 283 (accept_3_3 11 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 283 (Polychromatic418967fa.accept_19_9_6_17_1_3880 9 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 283 (accept_3_3 8 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 177 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 283 (accept_3_3 5 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 283 (accept_3_3 2 177 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 176 283 (Eq.refl Bool.true) (allA_of_3_1 108 176 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 175 283 (Eq.refl Bool.true) (allA_succ_of_accept 108 175 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 108 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 175 283 (accept_3_3 107 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 175 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 106 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 175 283 (Polychromatic418967fa.accept_19_10_4_17_1_1544 105 175 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 175 283 (accept_3_3 104 175 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 175 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 103 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 175 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 102 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 175 283 (accept_3_3 101 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 175 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 175 283
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 99 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 175 283 (accept_3_3 98 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 97 175 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 175 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 96 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 175 283 (accept_3_3 95 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 175 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 94 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 175 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 93 175 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 175 283 (accept_3_3 92 175 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 175 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 175 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 90 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 175 283 (accept_3_3 89 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 175 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 88 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 175 283 (accept_3_3 86 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 175 283 (Polychromatic418967fa.accept_20_5_15_3_1_4516 85 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 175 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 175 283 (accept_3_3 83 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 175 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 82 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 175 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 81 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 175 283 (accept_3_3 80 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 175 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 79 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 175 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 78 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 175 283 (accept_3_3 77 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 175 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 175 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 75 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 175 283 (accept_3_3 74 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 175 283 (Polychromatic418967fa.accept_22_7_21_19_1_11342 73
  175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 175 283 (accept_3_3 71 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 175 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 70 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 175 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 69 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 283 (accept_3_3 68 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 175 283
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 66 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 175 283 (accept_3_3 65 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 175 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 64 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 175 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 283 (accept_3_3 62 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 61 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 175 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 175 283 (accept_3_3 59 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 175 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 58 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 283 (accept_3_3 56 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 175 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 283
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 283 (accept_3_3 53 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 283 (accept_3_3 50 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 283 (accept_3_3 47 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 283 (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 283 (accept_3_3 44 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 283 (accept_3_3 41 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 283 (Polychromatic418967fa.accept_17_6_5_11_1_4073 40 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 283 (accept_3_3 38 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 283 (accept_3_3 35 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 34 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 33 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 283 (accept_3_3 32 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 283
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 283 (accept_3_3 29 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 283 (accept_3_3 26 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 283
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 283 (accept_3_3 23 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 283 (Polychromatic418967fa.accept_19_2_4_17_1_12087 21 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 283 (accept_3_3 20 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 283 (accept_3_3 17 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 283 (accept_3_3 14 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 283 (Polychromatic418967fa.accept_19_13_4_17_1_5166 13 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 283 (accept_3_3 11 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 283 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 175 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 283 (accept_3_3 8 175 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 283
  (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 283 (accept_3_3 5 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 175 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 283 (accept_3_3 2 175 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 175
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 174 283 (Eq.refl Bool.true) (allA_succ_of_accept 109 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  109 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 174 283
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 108 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 174 283 (accept_3_3 107 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 174 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 174 283 (accept_3_3 104 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 174 283
  (Polychromatic418967fa.accept_19_8_3_17_1_5181 103 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 174 283 (accept_3_3 101 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 174
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 174 283
  (Polychromatic418967fa.accept_10_9_4_3_1_539 99 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 174 283 (accept_3_3 98 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 174 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 174 283 (accept_3_3 95 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 174 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 94 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 174 283 (accept_3_3 92 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 174 283 (Polychromatic418967fa.accept_19_14_3_17_1_6558 90 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 174 283 (accept_3_3 89 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 174 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 174 283 (accept_3_3 86 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 174 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 84 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 174 283 (accept_3_3 83 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 174 283 (accept_3_3 80 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 174 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 174 283 (accept_3_3 77 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 174 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 76 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 174 283
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 75 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 174 283 (accept_3_3 74 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 174 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 174 283 (accept_3_3 71 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218
  70 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 174 283 (accept_3_3 68 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 174 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 174 283 (accept_3_3 65 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 174 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 174 283 (accept_3_3 62 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 174 283 (accept_3_3 59 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 174 283 (accept_3_3 56 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 174 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 174 283 (accept_3_3 53 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 174 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 174 283 (accept_3_3 50 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 174 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 174 283 (accept_3_3 47 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 174 283 (accept_3_3 44 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 174 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 283 (accept_3_3 41 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 283 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 174 283 (accept_3_3 38 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 174 283 (Polychromatic418967fa.accept_21_15_6_10_1_10016 36 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 283 (accept_3_3 35 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 174 283 (accept_3_3 32 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 174 283 (Polychromatic418967fa.accept_19_12_3_17_1_5182 31 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 283 (accept_3_3 29 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 174 283 (accept_3_3 26 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 174 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 283 (accept_3_3 23 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 174 283 (accept_3_3 20 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 283 (accept_3_3 17 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 174 283 (accept_3_3 14 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 174 283 (Polychromatic418967fa.accept_19_12_3_17_1_5182 12 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 283 (accept_3_3 11 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 174 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 174 283 (accept_3_3 8 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  174 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 174 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 283 (accept_3_3 5 174 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 174 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 174 283 (accept_3_3 2 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  174 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 173 283 (Eq.refl Bool.true) (allA_of_3_1 111 173 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 172 283 (Eq.refl Bool.true) (allA_succ_of_accept 111 172 283 (Polychromatic418967fa.accept_6_3_4_1_1_8
  111 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 172 283 (accept_3_3
  110 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 172 283
  (Polychromatic418967fa.accept_18_1_10_13_1_500 109 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 172 283 (Polychromatic418967fa.accept_23_16_11_7_1_15890 108 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 172 283 (accept_3_3 107 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 172
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 172 283 (accept_3_3 104 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 172 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 103 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 172 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 172 283 (accept_3_3 101 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 172 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 100
  172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 172 283 (accept_3_3 98 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 172 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 172 283 (accept_3_3 95 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 172 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 172 283 (accept_3_3 92 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 172 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 91 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 172 283 (accept_3_3 89 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 172 283 (accept_3_3 86 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 172 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 172 283 (accept_3_3 83 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 172 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 172 283 (accept_3_3 80 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 172 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 172 283 (accept_3_3 77 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 172 283 (accept_3_3 74 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 172 283 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 172 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 172 283 (accept_3_3 71 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 172 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 172 283 (accept_3_3 68 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 172 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 67 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 172 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 172 283 (accept_3_3 65 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 172 283 (accept_3_3 62 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 172 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 172 283 (accept_3_3 59 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 172 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 172 283 (accept_3_3 56 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 172 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 54 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 283 (accept_3_3 53 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 172 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 172 283 (accept_3_3 50 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 172 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 49 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 283 (accept_3_3 47 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 172 283 (accept_3_3 44 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 172 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 283 (accept_3_3 41 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 283 (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 172 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 283 (accept_3_3 38 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 283 (accept_3_3 35 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 283 (accept_3_3 32 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 283 (accept_3_3 29 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 283 (accept_3_3 26 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 283 (accept_3_3 23 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 283 (accept_3_3 20 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 19 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 283 (Polychromatic418967fa.accept_19_18_1_17_1_12076 18 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 283 (accept_3_3 17 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 172 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 283 (accept_3_3 14 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 283 (accept_3_3 11 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 283 (accept_3_3 8 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 283 (accept_3_3 5 172 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 172 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 283 (accept_3_3 2 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 171 283 (Eq.refl Bool.true) (allA_succ_of_accept 112 171 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 171 283 (Polychromatic418967fa.accept_18_3_9_13_1_1235 111 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 171 283 (accept_3_3 110 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 171 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 109 171 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 171 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 108 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 171 283 (accept_3_3 107 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 105 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 171 283 (accept_3_3 104 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 283 (Polychromatic418967fa.accept_13_12_2_10_1_2698 103
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 171 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 102 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 171 283 (accept_3_3 101 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 171 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 99 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 171 283 (accept_3_3 98 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 171 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 97 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 171 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 96 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 171 283 (accept_3_3 95 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 93 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 171 283 (accept_3_3 92 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 91 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 171 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 90 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 171 283 (accept_3_3 89 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 283 (Polychromatic418967fa.accept_22_21_17_19_1_15910 87
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 171 283 (accept_3_3 86
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 171 283
  (Polychromatic418967fa.accept_21_1_3_10_1_5401 85 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 171 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 84 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 171 283 (accept_3_3 83 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  81 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 283 (accept_3_3 80
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 283
  (Polychromatic418967fa.accept_15_4_6_13_1_956 79 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 171 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 171 283 (accept_3_3 77 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 283
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 75 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 171 283 (accept_3_3 74 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 171 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 73 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 171 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 171 283 (accept_3_3 71 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 171 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 171 283 (accept_3_3 68 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 171 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 67 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 171 283 (Polychromatic418967fa.accept_23_20_10_7_1_15862 66 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 283 (accept_3_3 65 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 171 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 283
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 171 283 (accept_3_3 62 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 171 283 (Polychromatic418967fa.accept_17_10_1_11_1_2900 61 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 283 (Polychromatic418967fa.accept_13_8_2_10_1_652
  60 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 283 (accept_3_3 59
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 57 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 283 (accept_3_3 56 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 171 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 55 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 283
  (Polychromatic418967fa.accept_20_14_11_3_1_9060 54 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 171 283 (accept_3_3 53 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 283 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 283 (accept_3_3 50 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 283
  (Polychromatic418967fa.accept_15_4_6_13_1_956 49 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 171 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 283 (accept_3_3 47 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 283 (accept_3_3 44
  171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 283
  (Polychromatic418967fa.accept_21_1_3_10_1_5401 43 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 171 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 283 (accept_3_3 41 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 283
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 39 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 283 (accept_3_3 38 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 171 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 283 (accept_3_3 35 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 171 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 283 (accept_3_3 32 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 283 (Polychromatic418967fa.accept_20_10_11_3_1_1977 30 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 283 (accept_3_3 29 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 283
  (Polychromatic418967fa.accept_17_10_1_11_1_2900 27 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 283 (accept_3_3 26 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 283 (accept_3_3 23 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 283 (accept_3_3 20 171 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 171 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 283 (accept_3_3 17 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 283 (Polychromatic418967fa.accept_21_15_3_10_1_8533 15 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 283 (accept_3_3 14 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 283 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 171
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 283 (accept_3_3 11 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 283 (accept_3_3 8 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 283 (accept_3_3 5 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 283 (accept_3_3 2 171 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 283 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 171 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 170 283 (Eq.refl Bool.true) (allA_of_3_1 114 170 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 169 283 (Eq.refl Bool.true) (allA_succ_of_accept 114 169 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 169 283 (accept_3_3 113 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 169 283 (Polychromatic418967fa.accept_18_4_7_13_1_3303 112 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 169 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 111 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 169 283 (accept_3_3 110 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 169
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 169 283
  (Polychromatic418967fa.accept_21_3_1_10_1_10008 108 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 169 283 (accept_3_3 107 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 169 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 169
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 169 283 (accept_3_3 104 169
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 169 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 103 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 169 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 283 (accept_3_3 101 169 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 169 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 283
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 99 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 283 (accept_3_3 98 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 283 (Polychromatic418967fa.accept_17_12_16_11_1_7885 97 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 169 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 283 (accept_3_3 95 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 283 (accept_3_3 92 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 283 (accept_3_3 89 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 169 283 (accept_3_3 86 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 169 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 85 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 169 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 283 (accept_3_3 83 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 283 (accept_3_3 80 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 283 (accept_3_3 77 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 283 (accept_3_3 74 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 283 (accept_3_3 71 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 283 (accept_3_3 68 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 283 (accept_3_3 65 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 283
  (Polychromatic418967fa.accept_17_12_16_11_1_7885 63 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 169 283 (accept_3_3 62 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 169 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 169 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 283 (accept_3_3 59 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 283 (accept_3_3 56 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 283 (accept_3_3 53 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 283 (Polychromatic418967fa.accept_16_4_9_11_1_7159 52 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 283 (accept_3_3 50 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 283 (Polychromatic418967fa.accept_17_15_16_11_1_4001 49 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 283 (accept_3_3 47 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 283 (accept_3_3 44 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 283 (Polychromatic418967fa.accept_25_18_19_8_1_17373 43 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 283 (accept_3_3 41 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 283 (accept_3_3 38 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 283 (accept_3_3 35 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 283 (accept_3_3 32 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 283 (Polychromatic418967fa.accept_17_14_16_11_1_3997 31 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 283 (accept_3_3 29 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 169 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 283
  (Polychromatic418967fa.accept_23_4_8_7_1_15872 27 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 283 (accept_3_3 26 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 283 (accept_3_3 23 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 283 (accept_3_3 20 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 283 (accept_3_3 17 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 283 (accept_3_3 14 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 283 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 283 (accept_3_3 11 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 283 (accept_3_3 8 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 283 (accept_3_3 5 169 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 283 (accept_3_3 2 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 168 283 (Eq.refl Bool.true) (allA_succ_of_accept 115 168 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 115 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 168 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 114 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 168 283 (accept_3_3 113 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 112 168 283 (Polychromatic418967fa.accept_13_8_12_10_1_4414 112 168 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 168 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 111 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 168 283 (accept_3_3 110 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 109 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 168 283 (Polychromatic418967fa.accept_16_12_8_11_1_2695 108 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 168 283 (accept_3_3 107 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 168 283
  (Polychromatic418967fa.accept_10_5_8_3_1_229 105 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 168 283 (accept_3_3 104 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 168 283 (Polychromatic418967fa.accept_19_8_16_17_1_6552 103 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 168 283 (accept_3_3 101 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 168 283
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 99 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 168 283 (accept_3_3 98 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 168 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 168 283 (accept_3_3 95 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 168 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 94 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 168 283 (accept_3_3 92 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 168 283
  (Polychromatic418967fa.accept_17_5_15_11_1_3978 90 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 168 283 (accept_3_3 89 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 168 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 87 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 168 283 (accept_3_3 86 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 168 283
  (Polychromatic418967fa.accept_10_5_8_3_1_229 85 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 168 283 (accept_3_3 83 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 168 283 (Polychromatic418967fa.accept_10_1_8_3_1_947
  81 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 168 283 (accept_3_3 80
  168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 168 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 168 283 (Polychromatic418967fa.accept_19_2_16_17_1_12112 78 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 168 283 (accept_3_3 77 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 168 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 168 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 168 283 (accept_3_3 74 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 168 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 72 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 168 283 (accept_3_3 71 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 168 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 168 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 168 283 (accept_3_3 68 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 168 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 168 283 (accept_3_3 65 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 168 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 168 283 (accept_3_3 62 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 168 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 168 283 (accept_3_3 59 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 283
  (Polychromatic418967fa.accept_13_6_12_10_1_690 58 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 283 (accept_3_3 56 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 283
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 168 283 (accept_3_3 53 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 168 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 283 (accept_3_3 50 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 168 283 (accept_3_3 47 168 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 283 (Polychromatic418967fa.accept_10_5_8_3_1_229
  45 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 283 (accept_3_3 44
  168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 168 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 168 283 (accept_3_3 41 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 168 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 168 283 (accept_3_3 38 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 168 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 283 (accept_3_3 35 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 168 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 283
  (Polychromatic418967fa.accept_13_7_12_10_1_640 33 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 168 283 (accept_3_3 32 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 168 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 283 (accept_3_3 29 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 168 283 (accept_3_3 26 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 168 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 283 (accept_3_3 23 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 168
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 168 283 (accept_3_3 20 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 168 283 (Polychromatic418967fa.accept_19_18_16_17_1_2626 18 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 283 (accept_3_3 17 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 168 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 283
  (Polychromatic418967fa.accept_10_5_8_3_1_229 15 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 168 283 (accept_3_3 14 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 168 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 168 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 283 (accept_3_3 11 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 168 283 (accept_3_3 8 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  168 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 168 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 283 (accept_3_3 5 168 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 168 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 283 (accept_3_3 2 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 167 283 (Eq.refl Bool.true) (allA_of_3_1 117 167 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 166 283 (Eq.refl Bool.true) (allA_succ_of_accept 117 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  117 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 166 283 (accept_3_3
  116 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 166 283
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 115 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 166 283 (accept_3_3 113 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 166 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 112 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 111 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 166 283 (accept_3_3 110 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 166 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 166 283 (accept_3_3 107 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 166 283 (accept_3_3 104 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 166 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 103 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 166 283 (Polychromatic418967fa.accept_15_12_1_13_1_3444 102 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 166 283 (accept_3_3 101 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 166 283 (accept_3_3 98 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 166 283 (Polychromatic418967fa.accept_19_1_14_17_1_6605 96 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 166 283 (accept_3_3 95 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 166 283 (Polychromatic418967fa.accept_22_6_12_19_1_12877 94
  166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 166 283 (accept_3_3 92 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 166 283 (Polychromatic418967fa.accept_17_6_13_11_1_995 91 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 166 283 (Polychromatic418967fa.accept_22_2_12_19_1_12878 90 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 166 283 (accept_3_3 89 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 166 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 166 283 (accept_3_3 86 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 166 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 84 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 166 283 (accept_3_3 83 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 166 283 (Polychromatic418967fa.accept_16_2_6_11_1_1722 82 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 166 283 (accept_3_3 80 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 166 283 (accept_3_3 77 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 166 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 166 283 (accept_3_3 74 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 166 283 (accept_3_3 71 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 166 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 166 283 (accept_3_3 68 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 166 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 166 283 (Polychromatic418967fa.accept_16_2_6_11_1_1722 66 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 166 283 (accept_3_3 65 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 166 283 (accept_3_3 62 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 166 283 (Polychromatic418967fa.accept_19_3_14_17_1_6603 60 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 166 283 (accept_3_3 59 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 166 283 (accept_3_3 56 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 166 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 166 283 (Polychromatic418967fa.accept_19_16_14_17_1_3863 54 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 166 283 (accept_3_3 53 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 166 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 166 283 (accept_3_3 50 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 166 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 283 (accept_3_3 47 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 166 283 (Polychromatic418967fa.accept_17_12_13_11_1_2910 46
  166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 166 283 (accept_3_3 44 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 166 283 (Polychromatic418967fa.accept_15_12_1_13_1_3444 42 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 283 (accept_3_3 41 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 166 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 283 (accept_3_3 38 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 283 (accept_3_3 35 166 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 283 (Polychromatic418967fa.accept_16_2_6_11_1_1722 34 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 283 (accept_3_3 32 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 283 (Polychromatic418967fa.accept_19_12_14_17_1_17372 31 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 283 (accept_3_3 29 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 283 (accept_3_3 26 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 283 (Polychromatic418967fa.accept_17_7_13_11_1_2895 24 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 283 (accept_3_3 23 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 283 (accept_3_3 20 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 283 (accept_3_3 17 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 283 (accept_3_3 14 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 283 (Polychromatic418967fa.accept_15_12_1_13_1_3444 12 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 283 (accept_3_3 11 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 166
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 283 (accept_3_3 8 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 283 (Polychromatic418967fa.accept_17_6_13_11_1_995 6 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 283 (accept_3_3 5 166 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 166 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 283 (accept_3_3 2 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 165 283 (Eq.refl Bool.true) (allA_succ_of_accept 118 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 118 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 165 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 117 165 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 165 283 (accept_3_3 116 165 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 165 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 115 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 165 283 (accept_3_3 113 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 111 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 165 283 (accept_3_3 110 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 165 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 165
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 165 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 108 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 165 283 (accept_3_3 107 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 165 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 165 283 (accept_3_3 104 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 103
  165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 165 283 (accept_3_3 101 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 165 283 (accept_3_3 98 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 165 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 165 283 (accept_3_3 95 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 165 283 (Polychromatic418967fa.accept_21_9_18_10_1_5388 93 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 165 283 (accept_3_3 92 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 165 283 (accept_3_3 89 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 165 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 283 (accept_3_3 86 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 165 283
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 84 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 165 283 (accept_3_3 83 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 165 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 81 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 165 283 (accept_3_3 80 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 165 283 (accept_3_3 77 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 165 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 75 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 283 (accept_3_3 74 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 165 283 (accept_3_3 71 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 283 (accept_3_3 68 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 165 283 (accept_3_3 65 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 283 (accept_3_3 62 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 165 283 (accept_3_3 59 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 283 (accept_3_3 56 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 283 (accept_3_3 53 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 283 (accept_3_3 50 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 165 283 (accept_3_3 47 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 165 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 283 (accept_3_3 44 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 283 (accept_3_3 41 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 283 (accept_3_3 38 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 165 283 (accept_3_3 35 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 165 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 283 (accept_3_3 32 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 283 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 283 (accept_3_3 29 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 283 (accept_3_3 26 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 283 (accept_3_3 23 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 283 (accept_3_3 20 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 283 (accept_3_3 17 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 283 (accept_3_3 14 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 283 (accept_3_3 11 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 283 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 283 (accept_3_3 8 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 165 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 283 (accept_3_3 5 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 283 (accept_3_3 2 165 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 164 283 (Eq.refl Bool.true) (allA_of_3_1 120 164 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 121 163 283 (Eq.refl Bool.true) (allA_succ_of_accept 120 163 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 120 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 163 283 (accept_3_3 119 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 118 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 117 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 163 283 (accept_3_3 116 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 163
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 163 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 114 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 163 283 (accept_3_3 113 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 163 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 112 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 111 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 163 283 (accept_3_3 110 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 163 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 109
  163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 163 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 108 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 163 283 (accept_3_3 107 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 163 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 163 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 105 163
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 163 283 (accept_3_3 104 163
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 163 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 103 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 163 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 163 283 (accept_3_3 101 163 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 163 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 100 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 163 283 (accept_3_3 98 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 283 (accept_3_3 95 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 163 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 94 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 283 (accept_3_3 92 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 283 (Polychromatic418967fa.accept_21_7_16_10_1_1349 91 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 283 (accept_3_3 89 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 283 (accept_3_3 86 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 283 (accept_3_3 83 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 283
  (Polychromatic418967fa.accept_13_3_7_10_1_668 81 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 283 (accept_3_3 80 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 283 (accept_3_3 77 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 283 (accept_3_3 74 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 283 (Polychromatic418967fa.accept_16_8_3_11_1_4763 72 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 283 (accept_3_3 71 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 283 (accept_3_3 68 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 283 (Polychromatic418967fa.accept_21_4_16_10_1_10019 67 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 283 (accept_3_3 65 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 283
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 63 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 163 283 (accept_3_3 62 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 163 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 283 (accept_3_3 59 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 283
  (Polychromatic418967fa.accept_22_14_9_19_1_17363 58 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 283 (accept_3_3 56 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 283 (accept_3_3 53 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 283 (accept_3_3 50 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 283 (Polychromatic418967fa.accept_21_7_16_10_1_1349 49 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 283 (accept_3_3 47 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 283 (Polychromatic418967fa.accept_16_14_3_11_1_5969 46 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 283 (Polychromatic418967fa.accept_21_3_16_10_1_3911 45 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 283 (accept_3_3 44 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 283 (accept_3_3 41 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 283 (accept_3_3 38 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 283 (Polychromatic418967fa.accept_17_3_10_11_1_7848 37 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 283 (accept_3_3 35 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 283 (accept_3_3 32 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 283 (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 283 (accept_3_3 29 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 283 (accept_3_3 26 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 283 (accept_3_3 23 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 283 (accept_3_3 20 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 283
  (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 163 283 (accept_3_3 17 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 283 (accept_3_3 14 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 283 (Polychromatic418967fa.accept_7_6_2_3_1_107
  13 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 283 (accept_3_3 11 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 283 (Polychromatic418967fa.accept_19_9_11_17_1_9445 9 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 283 (accept_3_3 8 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 283 (accept_3_3 5 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 163 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 283 (accept_3_3 2 163 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 162 283 (Eq.refl Bool.true) (allA_succ_of_accept 121 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  121 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 162 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 120 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 162 283 (accept_3_3 119 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 162 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 118 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  117 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 162 283 (accept_3_3
  116 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 162 283
  (Polychromatic418967fa.accept_10_5_2_3_1_239 115 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 162 283 (accept_3_3 113 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 162 283 (Polychromatic418967fa.accept_21_7_15_10_1_1368 112 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 162 283
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 111 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 162 283 (accept_3_3 110 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 162 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 108 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 162 283 (accept_3_3 107 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 162 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 106
  162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 162 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 162 283 (accept_3_3 104 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 162 283 (accept_3_3 101 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 162
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 162 283
  (Polychromatic418967fa.accept_19_4_10_17_1_5194 99 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 162 283 (accept_3_3 98 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 162 283 (accept_3_3 95 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 162 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 94 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 162 283 (accept_3_3 92 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 162 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 91 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 162 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 90 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 162 283 (accept_3_3 89 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 162 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 87 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 162 283 (accept_3_3 86 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 162 283
  (Polychromatic418967fa.accept_19_8_10_17_1_12082 84 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 162 283 (accept_3_3 83 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 162 283 (accept_3_3 80 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  79 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 162 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 78 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 162 283 (accept_3_3 77 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 162 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 76 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 162 283 (accept_3_3 74 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 162 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 162 283 (accept_3_3 71 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 162 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 70 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 162 283 (accept_3_3 68 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 283
  (Polychromatic418967fa.accept_21_3_15_10_1_3895 66 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 162 283 (accept_3_3 65 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 162 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 64 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 162 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 63 162
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 283 (accept_3_3 62 162
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  61 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 162 283 (accept_3_3 59 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 283 (accept_3_3 56 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 283 (accept_3_3 53 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 162 283 (Polychromatic418967fa.accept_23_6_1_7_1_9415 52 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 283 (accept_3_3 50 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 283
  (Polychromatic418967fa.accept_13_9_6_10_1_666 48 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 283 (accept_3_3 47 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 283 (accept_3_3 44 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 162 283 (accept_3_3 41 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 283 (accept_3_3 38 162 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 283
  (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 162 283 (accept_3_3 35 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 162 283 (Polychromatic418967fa.accept_19_15_10_17_1_3859 34 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 283 (accept_3_3 32 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 162
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 283 (accept_3_3 29 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 283 (Polychromatic418967fa.accept_19_8_10_17_1_12082 27 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 283 (accept_3_3 26 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 283
  (Polychromatic418967fa.accept_21_3_15_10_1_3895 24 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 162 283 (accept_3_3 23 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 22 162 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 283 (accept_3_3 20 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 283 (Polychromatic418967fa.accept_7_5_1_3_1_103
  19 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 283 (accept_3_3 17 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 283 (accept_3_3 14 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 283 (accept_3_3 11 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 283 (accept_3_3 8 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 283 (Polychromatic418967fa.accept_16_7_2_11_1_931 7 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 283
  (Polychromatic418967fa.accept_16_6_2_11_1_7132 6 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 283 (accept_3_3 5 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 283 (accept_3_3 2 162 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 161 283 (Eq.refl Bool.true) (allA_of_3_1 123 161 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 124 160 283 (Eq.refl Bool.true) (allA_succ_of_accept 123 160 283 (Polychromatic418967fa.accept_6_3_4_1_1_8
  123 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 160 283 (accept_3_3
  122 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 160 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 121 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 160 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 120 160 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 160 283 (accept_3_3 119 160 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 118 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 117 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 160 283 (accept_3_3 116 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 160 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 115 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 114 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 160 283 (accept_3_3 113 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 160 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 112
  160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 111 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 160 283 (accept_3_3 110 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 160 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 108 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 160 283 (accept_3_3 107 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 160 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 106 160
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 160 283 (accept_3_3 104 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 160 283 (Polychromatic418967fa.accept_17_1_7_11_1_2892 103 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 160 283 (accept_3_3 101 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 160
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 160 283 (accept_3_3 98 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 160 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 97 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 160 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 160 283 (accept_3_3 95 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 160 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 160 283 (accept_3_3 92 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 160 283 (Polychromatic418967fa.accept_17_5_7_11_1_5274 90 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 160 283 (accept_3_3 89 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 160 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 160 283 (accept_3_3 86 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 160 283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 85 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 160 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 160 283 (accept_3_3 83 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 160 283 (accept_3_3 80 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 160 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 160 283 (accept_3_3 77 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 160 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 76 160 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 160 283 (accept_3_3 74 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 160 283 (accept_3_3 71 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 160 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 160 283 (accept_3_3 68 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 160 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 160 283 (accept_3_3 65 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 160 283 (accept_3_3 62 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 160 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 160 283 (accept_3_3 59 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 160 283 (accept_3_3 56 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 160 283 (Polychromatic418967fa.accept_19_16_8_17_1_5148 54 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 283 (accept_3_3 53 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 160 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 160
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 160 283 (accept_3_3 50 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 160 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 160 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 283 (accept_3_3 47 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 160 283 (accept_3_3 44 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 283 (Polychromatic418967fa.accept_21_1_13_10_1_11627 43 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 283 (accept_3_3 41 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 160 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 160
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 160 283 (accept_3_3 38 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 160 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 283 (accept_3_3 35 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 160 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 160
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 160 283 (accept_3_3 32 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 160 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 160 283 (accept_3_3 29 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 283 (accept_3_3 26 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 160 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 283 (accept_3_3 23 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 160 283 (accept_3_3 20 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 283 (accept_3_3 17 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 160 283 (accept_3_3 14 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 283 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 283 (accept_3_3 11 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 283 (accept_3_3 8 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 283 (accept_3_3 5 160 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 283 (accept_3_3 2 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 160 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 159 283 (Eq.refl Bool.true) (allA_succ_of_accept 124 159 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 124 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 159 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 123 159 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 159 283 (accept_3_3 122 159 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 121 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 159 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 120 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 159 283 (accept_3_3 119 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 118 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 159 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 117 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 159 283 (accept_3_3 116 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 115 159
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 159 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 114 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 159 283 (accept_3_3 113 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 159 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 159 283 (accept_3_3 110 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 109 159
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 108 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 159 283 (accept_3_3 107 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 159 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 105 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 159 283 (accept_3_3 104 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 283 (Polychromatic418967fa.accept_16_7_15_11_1_951 103
  159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 102 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 159 283 (accept_3_3 101 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 159 283 (accept_3_3 98 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 283
  (Polychromatic418967fa.accept_10_6_9_3_1_935 96 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 159 283 (accept_3_3 95 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 283 (accept_3_3 92 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 283
  (Polychromatic418967fa.accept_11_2_5_8_1_470 90 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 159 283 (accept_3_3 89 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 159 283 (Polychromatic418967fa.accept_16_7_15_11_1_951 87 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 283 (accept_3_3 86 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 159 283 (accept_3_3 83 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 81 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 283 (accept_3_3 80 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 159 283 (accept_3_3 77 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 283 (accept_3_3 74 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 159 283 (accept_3_3 71 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 159 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 69 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 283 (accept_3_3 68 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 67 159
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 159 283 (accept_3_3 65 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 283 (accept_3_3 62 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 283 (accept_3_3 59 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 283 (accept_3_3 56 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 283 (accept_3_3 53 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 283 (accept_3_3 50 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 49 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 283 (accept_3_3 47 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 283 (accept_3_3 44 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 283
  (Polychromatic418967fa.accept_16_10_15_11_1_3785 42 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 283 (accept_3_3 41 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 283 (accept_3_3 38 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 283 (accept_3_3 35 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 283 (accept_3_3 32 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 283 (Polychromatic418967fa.accept_24_7_15_19_1_5392 31 159
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 283 (accept_3_3 29 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 283 (Polychromatic418967fa.accept_21_6_12_10_1_2576 27 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 283 (accept_3_3 26 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 159 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 283 (accept_3_3 23 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 283 (accept_3_3 20 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 283 (accept_3_3 17 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 283 (accept_3_3 14 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 283 (accept_3_3 11 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 283 (accept_3_3 8 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 283
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 283 (accept_3_3 5 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 283 (accept_3_3 2 159 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 158 283 (Eq.refl Bool.true) (allA_of_3_1 126 158 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 127 157 283 (Eq.refl Bool.true) (allA_succ_of_accept 126 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 126 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 157 283 (accept_3_3 125 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 157 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 124 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 157 283 (Polychromatic418967fa.accept_23_8_19_7_1_11097 123 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 157 283 (accept_3_3 122 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 157 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 121 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 157 283
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 120 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 157 283 (accept_3_3 119 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 157 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 283 (Polychromatic418967fa.accept_17_15_4_11_1_6515 117
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 157 283 (accept_3_3 116
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 157 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 115 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 157 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 283 (accept_3_3 113 157 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 157 283 (Polychromatic418967fa.accept_17_10_4_11_1_4047 112 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 157 283
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 111 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 157 283 (accept_3_3 110 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 157 283 (Polychromatic418967fa.accept_19_14_5_17_1_6542 109 157 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 157 283
  (Polychromatic418967fa.accept_13_4_1_10_1_693 108 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 157 283 (accept_3_3 107 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 157 283 (accept_3_3 104 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 157 283 (Polychromatic418967fa.accept_22_15_3_19_1_12887 103
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 157 283 (accept_3_3 101 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 157 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 100 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 157 283 (Polychromatic418967fa.accept_15_9_7_13_1_1664 99 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 157 283 (accept_3_3 98 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 157 283 (Polychromatic418967fa.accept_19_2_5_17_1_3850 97 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 157 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 96 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 157 283 (accept_3_3 95 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 157 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 93 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 157 283 (accept_3_3 92 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 157 283 (Polychromatic418967fa.accept_17_6_4_11_1_4072 91 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 157 283 (accept_3_3 89 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 157 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 88 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 157 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 87 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 283 (accept_3_3 86 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 84 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 283 (accept_3_3 83 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 81 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 283 (accept_3_3 80 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 283 (Polychromatic418967fa.accept_19_3_5_17_1_9438 79 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 283 (accept_3_3 77 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 76 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 283 (accept_3_3 74 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 283 (Polychromatic418967fa.accept_22_7_3_19_1_8158 73 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 72 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 283 (accept_3_3 71 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 69 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 283 (accept_3_3 68 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 283 (Polychromatic418967fa.accept_23_21_19_7_1_15886 67
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 283 (accept_3_3 65 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 283 (accept_3_3 62 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 61 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 60 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 283 (accept_3_3 59 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 283 (Polychromatic418967fa.accept_17_6_4_11_1_4072 57 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 283 (accept_3_3 56 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 283 (accept_3_3 53 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 283 (Polychromatic418967fa.accept_19_14_5_17_1_6542 52 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 51 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 283 (accept_3_3 50 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 283
  (Polychromatic418967fa.accept_13_9_1_10_1_647 48 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 283 (accept_3_3 47 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 283 (accept_3_3 44 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 43 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 283 (accept_3_3 41 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 40 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 283 (accept_3_3 38 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 37 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 283 (accept_3_3 35 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 283 (Polychromatic418967fa.accept_19_14_5_17_1_6542 33 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 283 (accept_3_3 32 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 283 (Polychromatic418967fa.accept_19_12_5_17_1_9439 31 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 283 (accept_3_3 29 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 283 (accept_3_3 26 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 283 (accept_3_3 23 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 283 (accept_3_3 20 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 283 (Polychromatic418967fa.accept_28_19_17_3_1_17339 19
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 283 (accept_3_3 17 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 283 (accept_3_3 14 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 283 (Polychromatic418967fa.accept_23_13_19_7_1_17327 13
  157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 283
  (Polychromatic418967fa.accept_19_12_5_17_1_9439 12 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 157 283 (accept_3_3 11 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 157 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 157 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 283 (accept_3_3 8 157 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 283 (Polychromatic418967fa.accept_19_7_5_17_1_3849
  7 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 283 (accept_3_3 5 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 157 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 283 (Polychromatic418967fa.accept_19_3_5_17_1_9438 3 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 283 (accept_3_3 2 157 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 283 (Polychromatic418967fa.accept_24_1_13_19_1_2191 1 157
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 156 283 (Eq.refl Bool.true) (allA_succ_of_accept 127 156 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 127 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 156 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 126 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 156 283 (accept_3_3 125 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 124 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 156 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 123 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 156 283 (accept_3_3 122 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 156 283 (Polychromatic418967fa.accept_17_2_3_11_1_2919 121 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 156 283 (accept_3_3 119 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 118 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 156 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 117 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 156 283 (accept_3_3 116 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 156 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 115 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 156 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 114 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 156 283 (accept_3_3 113 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 156 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 112 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 156 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 156 283 (accept_3_3 110 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 156 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 156 283 (accept_3_3 107 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 156 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 156 283 (accept_3_3 104 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 156 283 (Polychromatic418967fa.accept_21_18_9_10_1_2571 102 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 156 283 (accept_3_3 101 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 156 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 156 283 (accept_3_3 98 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 156 283 (accept_3_3 95 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 156 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 94 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 156 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 93 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 156 283 (accept_3_3 92 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 156 283 (accept_3_3 89 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 156 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 156 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 87 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 156 283 (accept_3_3 86 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 156 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 84 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 156 283 (accept_3_3 83 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 156 283
  (Polychromatic418967fa.accept_16_1_12_11_1_2648 81 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 156 283 (accept_3_3 80 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 156 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 156 283 (accept_3_3 77 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107
  76 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 156 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 156 283 (accept_3_3 74 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 156 283 (Polychromatic418967fa.accept_16_8_12_11_1_3697 72 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 156 283 (accept_3_3 71 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 156 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 156 283 (accept_3_3 68 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 156 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 156 283 (Polychromatic418967fa.accept_21_3_9_10_1_6992 66 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 156 283 (accept_3_3 65 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 156 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 63 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 156 283 (accept_3_3 62 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 156 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 156 283 (accept_3_3 59 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 156 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 156 283 (accept_3_3 56 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 156 283 (accept_3_3 53 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 156 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 156 283 (accept_3_3 50 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 156 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 156 283 (accept_3_3 47 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 156 283
  (Polychromatic418967fa.accept_21_3_9_10_1_6992 45 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 156 283 (accept_3_3 44 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 156 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 156 283 (accept_3_3 41 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 156 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 156 283 (accept_3_3 38 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 283 (accept_3_3 35 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 156 283 (accept_3_3 32 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 156 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 156 283 (Polychromatic418967fa.accept_19_11_4_17_1_2617 30 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 283 (accept_3_3 29 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 156 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 156 283 (accept_3_3 26 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 156 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 156 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 283 (accept_3_3 23 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 156 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 283
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 156 283 (accept_3_3 20 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 283 (accept_3_3 17 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 16 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 283 (accept_3_3 14 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 283 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 283 (accept_3_3 11
  156 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 10 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 156 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 283 (accept_3_3 8 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 156 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 283 (accept_3_3 5 156
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 283
  (Polychromatic418967fa.accept_15_4_6_13_1_956 4 156 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 156 283 (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 283 (accept_3_3 2 156 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 156 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 155 283 (Eq.refl Bool.true) (allA_of_3_1 129 155 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 130 154 283 (Eq.refl Bool.true) (allA_succ_of_accept 129 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  129 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 154 283 (accept_3_3
  128 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 154 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 127 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 154 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 126 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 154 283 (accept_3_3 125 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 124 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 124 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 123 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 154 283 (accept_3_3 122 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 120 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 154 283 (accept_3_3 119 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 154 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 118
  154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 154 283 (accept_3_3 116 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 114 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 154 283 (accept_3_3 113 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 112 154
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 111 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 154 283 (accept_3_3 110 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 154 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 108 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 154 283 (accept_3_3 107 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 154
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 154 283 (accept_3_3 104 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 154 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 103 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 154 283 (accept_3_3 101 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 154
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 154 283 (accept_3_3 98 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 154 283 (accept_3_3 95 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 154 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 94 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 154 283 (accept_3_3 92 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 154 283 (Polychromatic418967fa.accept_18_1_10_13_1_500 91 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 154 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 90 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 154 283 (accept_3_3 89 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 154 283 (accept_3_3 86 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 154 283 (accept_3_3 83 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 154 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 82 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 154 283 (accept_3_3 80 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 154 283 (accept_3_3 77 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 154 283 (accept_3_3 74 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 154 283 (Polychromatic418967fa.accept_19_15_2_17_1_5163 72 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 283 (accept_3_3 71 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 154 283 (accept_3_3 68 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 154 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 283 (accept_3_3 65 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 154 283 (accept_3_3 62 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 283 (accept_3_3 59 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 283 (Polychromatic418967fa.accept_17_7_1_11_1_1894 58 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 154 283 (accept_3_3 56 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 154 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 55 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 154 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 154 283 (accept_3_3 53 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 154 283 (accept_3_3 50 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 283 (accept_3_3 47 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 283 (Polychromatic418967fa.accept_25_21_4_8_1_17371 46 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 154 283 (accept_3_3 44 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 283 (accept_3_3 41 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 283 (accept_3_3 38 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 283 (accept_3_3 35 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 283 (accept_3_3 32 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 283 (Polychromatic418967fa.accept_16_15_10_11_1_1727 31 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 283 (accept_3_3 29 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 154
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 283 (accept_3_3 26 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 283 (accept_3_3 23 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 283 (Polychromatic418967fa.accept_18_4_10_13_1_5883 22 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 283 (accept_3_3 20 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 283 (Polychromatic418967fa.accept_21_18_7_10_1_13049 18 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 283 (accept_3_3 17 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 283 (accept_3_3 14 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 283 (accept_3_3 11 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 154 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 283 (accept_3_3 8 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 283 (accept_3_3 5 154 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 154 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 283 (accept_3_3 2 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 153 283 (Eq.refl Bool.true) (allA_succ_of_accept 130 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 130 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 153 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 129 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 153 283 (accept_3_3 128 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 127 153 283 (Polychromatic418967fa.accept_22_17_21_19_1_4790 127 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 126 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 153 283 (accept_3_3 125 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 124 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 153 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 123 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 153 283 (accept_3_3 122 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 121 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 153 283
  (Polychromatic418967fa.accept_21_15_6_10_1_10016 120 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 153 283 (accept_3_3 119 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 153 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 153 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 117
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 153 283 (accept_3_3 116
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 283
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 115 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 153 283 (accept_3_3 113 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 153 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 111 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 153 283 (accept_3_3 110 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 153 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 153 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 153 283 (accept_3_3 107 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 153 283
  (Polychromatic418967fa.accept_19_10_1_17_1_6595 105 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 153 283 (accept_3_3 104 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 153 283 (Polychromatic418967fa.accept_27_22_18_13_1_17357 103 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  102 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 153 283 (accept_3_3
  101 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 153 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 153 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 283 (accept_3_3 98 153 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 153 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 97 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 153 283
  (Polychromatic418967fa.accept_18_6_9_13_1_3320 96 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 153 283 (accept_3_3 95 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 153 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 283 (accept_3_3 92 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 91 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 153 283 (accept_3_3 89 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 153 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 283 (accept_3_3 86 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 85 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 84 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 153 283 (accept_3_3 83 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 153 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 283 (accept_3_3 80 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 153 283 (accept_3_3 77 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 75 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 283 (accept_3_3 74 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 283 (Polychromatic418967fa.accept_19_16_1_17_1_8065 73 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 283 (accept_3_3 71 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 283 (accept_3_3 68 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 153 283 (accept_3_3 65 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 283 (accept_3_3 62 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 153 283 (accept_3_3 59 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 153 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 57 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 283 (accept_3_3 56 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 55 153
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 283 (accept_3_3 53 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 283 (accept_3_3 50 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 283 (Polychromatic418967fa.accept_24_1_9_19_1_12488 49 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 283
  (Polychromatic418967fa.accept_19_10_1_17_1_6595 48 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 283 (accept_3_3 47 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 283 (Polychromatic418967fa.accept_23_22_15_7_1_17358 45
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 283 (accept_3_3 44
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 283
  (Polychromatic418967fa.accept_23_20_15_7_1_15875 43 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 283 (accept_3_3 41 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 283 (accept_3_3 38 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 283 (Polychromatic418967fa.accept_16_4_9_11_1_7159 36 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 283 (accept_3_3 35 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 283
  (Polychromatic418967fa.accept_19_14_1_17_1_8063 33 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 283 (accept_3_3 32 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 153 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 283 (accept_3_3 29 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 283 (accept_3_3 26 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 283 (accept_3_3 23 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 283
  (Polychromatic418967fa.accept_16_5_9_11_1_3762 21 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 283 (accept_3_3 20 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 283 (Polychromatic418967fa.accept_27_19_18_13_1_13724 19 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 283 (accept_3_3 17 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 283 (accept_3_3 14 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 283 (Polychromatic418967fa.accept_22_13_21_19_1_17370 13 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 283 (accept_3_3 11 153 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 283 (accept_3_3 8 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 283 (Polychromatic418967fa.accept_22_7_21_19_1_11342 7 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 283 (accept_3_3 5 153 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 283 (accept_3_3 2 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 153 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 152 283 (Eq.refl Bool.true) (allA_of_3_1 132 152 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 133 151 283 (Eq.refl Bool.true) (allA_succ_of_accept 132 151 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 132 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 151 283 (accept_3_3 131 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 151 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 130 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 129 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 129 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 151 283 (accept_3_3 128 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 127 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 151 283
  (Polychromatic418967fa.accept_19_12_18_17_1_8075 126 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 151 283 (accept_3_3 125 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 151 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 124 151 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 123 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 151 283 (accept_3_3 122 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 151 283
  (Polychromatic418967fa.accept_13_4_8_10_1_671 121 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 120 151 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 151 283 (accept_3_3 119 151 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 118 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 117 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 151 283 (accept_3_3 116 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 151 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 115 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212
  114 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 283 (accept_3_3
  113 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 112 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 111 151 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 151 283 (accept_3_3 110 151 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 151 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 108 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 151 283 (accept_3_3 107 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 151 283 (accept_3_3 104 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 151 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 103
  151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 151 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 151 283 (accept_3_3 101 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 151 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 151 283 (accept_3_3 98 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 151 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 151 283 (accept_3_3 95 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 151 283 (Polychromatic418967fa.accept_18_4_7_13_1_3303 94 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 93 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 151 283 (accept_3_3 92 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 151 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 151 283 (accept_3_3 89 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 151 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 88 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 283 (accept_3_3 86 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 151 283 (accept_3_3 83 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 151 283 (Polychromatic418967fa.accept_17_13_15_11_1_2936 81 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 283 (accept_3_3 80 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 79 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 283 (accept_3_3 77 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 283 (accept_3_3 74 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 72 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 283 (accept_3_3 71 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 70 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 283 (accept_3_3 68 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 283 (accept_3_3 65 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 283 (accept_3_3 62 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 283 (Polychromatic418967fa.accept_19_4_18_17_1_1511 61 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 283 (accept_3_3 59 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 283 (accept_3_3 56 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 283
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 283 (accept_3_3 53 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 283 (accept_3_3 50 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 283 (accept_3_3 47 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 283 (Polychromatic418967fa.accept_19_7_18_17_1_663 45 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 283 (accept_3_3 44 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 283 (accept_3_3 41 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 283 (accept_3_3 38 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 283 (accept_3_3 35 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 283 (accept_3_3 32 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 283 (accept_3_3 29 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 283 (accept_3_3 26 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 283 (accept_3_3 23 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 283 (accept_3_3 20 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 283 (accept_3_3 17 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 283 (Polychromatic418967fa.accept_17_16_15_11_1_10421 16 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 283 (accept_3_3 14 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 283 (accept_3_3 11 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 283 (Polychromatic418967fa.accept_25_9_1_8_1_17369 9 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 283 (accept_3_3 8 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 283 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 151
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 283 (accept_3_3 5 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 151 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 283 (accept_3_3 2 151 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 150 283 (Eq.refl Bool.true) (allA_succ_of_accept 133 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  133 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 150 283
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 132 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 131 150 283 (accept_3_3 131 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 150 283 (Polychromatic418967fa.accept_16_2_6_11_1_1722 130 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  129 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 150 283 (accept_3_3
  128 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 150 283
  (Polychromatic418967fa.accept_9_1_6_4_1_49 127 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 150 283 (Polychromatic418967fa.accept_26_22_20_23_1_8233 126 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 150 283 (accept_3_3 125 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 124 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 124 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 150 283
  (Polychromatic418967fa.accept_21_18_3_10_1_8534 123 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 150 283 (accept_3_3 122 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 120 150
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 150 283 (accept_3_3 119 150
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 150 283
  (Polychromatic418967fa.accept_9_1_6_4_1_49 118 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 150 283 (accept_3_3 116 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 115 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 150 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 114 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 150 283 (accept_3_3 113 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 150 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 112 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 150 283 (accept_3_3 110 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 150 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 108 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 150 283 (accept_3_3 107 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 150 283 (accept_3_3 104 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 150 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 103 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 150 283 (accept_3_3 101 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 150 283
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 99 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 150 283 (accept_3_3 98 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 150 283 (Polychromatic418967fa.accept_21_12_3_10_1_8575 96 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 150 283 (accept_3_3 95 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 150 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 94 150
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 150 283 (accept_3_3 92 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 150 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 90 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 150 283 (accept_3_3 89 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 150 283
  (Polychromatic418967fa.accept_20_7_10_3_1_949 87 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 150 283 (accept_3_3 86 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 150 283 (accept_3_3 83 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 150 283 (accept_3_3 80 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 150 283 (Polychromatic418967fa.accept_21_15_3_10_1_8533 78 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 150 283 (accept_3_3 77 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 76 150
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 150 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 150 283 (accept_3_3 74 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 150 283 (Polychromatic418967fa.accept_20_12_10_3_1_4537 72 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 150 283 (accept_3_3 71 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 150 283 (accept_3_3 68 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 150 283 (Polychromatic418967fa.accept_16_3_6_11_1_2718 67 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 150 283 (accept_3_3 65 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 150 283
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 150 283 (accept_3_3 62 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 150 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 150 283 (accept_3_3 59 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 283 (Polychromatic418967fa.accept_21_16_3_10_1_6978 58 150
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 150 283 (accept_3_3 56 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 150 283 (Polychromatic418967fa.accept_17_3_14_11_1_5243 54 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 283 (accept_3_3 53 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 283
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 150 283 (accept_3_3 50 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 283 (accept_3_3 47 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46
  150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 150 283 (accept_3_3 44 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 150 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 283 (accept_3_3 41 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 283 (Polychromatic418967fa.accept_23_17_12_7_1_17368 40
  150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 150 283 (accept_3_3 38 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 150 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 283 (accept_3_3 35 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 150 283 (accept_3_3 32 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 150 283 (Polychromatic418967fa.accept_20_11_10_3_1_10529 31 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 150 283 (accept_3_3 29 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 283
  (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 150 283 (accept_3_3 26 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 283 (Polychromatic418967fa.accept_26_24_20_23_1_10132 24
  150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 150 283 (accept_3_3 23
  150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 283
  (Polychromatic418967fa.accept_20_2_10_3_1_9059 22 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 283 (accept_3_3 20 150 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 283
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 283 (accept_3_3 17 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 283 (accept_3_3 14 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 283 (accept_3_3 11 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 283 (accept_3_3 8 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 283
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 283 (accept_3_3 5 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 150 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 283 (accept_3_3 2 150 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 149 283 (Eq.refl Bool.true) (allA_of_3_1 135 149 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 136 148 283 (Eq.refl Bool.true) (allA_succ_of_accept 135 148 283 (Polychromatic418967fa.accept_6_3_4_1_1_8
  135 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 148 283 (accept_3_3
  134 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 148 283
  (Polychromatic418967fa.accept_17_14_12_11_1_4063 133 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 148 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 132 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 148 283 (accept_3_3 131 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 130 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 129 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 148 283 (accept_3_3 128 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 148 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 127 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 126 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 148 283 (accept_3_3 125 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 124 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 123 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 148 283 (accept_3_3 122 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 121 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 148 283 (Polychromatic418967fa.accept_16_8_4_11_1_2687 120 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 148 283 (accept_3_3 119 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 118 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 117 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 148 283 (accept_3_3 116 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 148 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 115 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 148 283 (accept_3_3 113 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 148 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 112 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 111 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 148 283 (accept_3_3 110 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 148 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 108 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 148 283 (accept_3_3 107 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 106 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 148 283 (accept_3_3 104 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 148 283 (accept_3_3 101 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 148 283 (accept_3_3 98 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 148 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 97 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 148 283 (accept_3_3 95 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 148 283 (accept_3_3 92 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 148 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 91 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 148 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 148 283 (accept_3_3 89 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 148 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 148 283 (accept_3_3 86 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 148 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 85 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 148 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 84 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 148 283 (accept_3_3 83 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 148 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 148 283 (accept_3_3 80 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 148 283 (Polychromatic418967fa.accept_19_2_15_17_1_2614 78 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 148 283 (accept_3_3 77 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 148 283 (accept_3_3 74 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 148 283 (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 148 283 (accept_3_3 71 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 148 283 (accept_3_3 68 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 148 283 (accept_3_3 65 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 148 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 64
  148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 148 283 (accept_3_3 62 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 148 283 (accept_3_3 59 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 148 283 (accept_3_3 56 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 148 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 148 283 (accept_3_3 53 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 148 283 (Polychromatic418967fa.accept_19_14_15_17_1_3877 52 148 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 148 283 (accept_3_3 50 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 148 283 (Polychromatic418967fa.accept_21_7_1_10_1_8571 49 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 148 283 (Polychromatic418967fa.accept_17_14_12_11_1_4063 48 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 148 283 (accept_3_3 47 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 148 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 148 283 (accept_3_3 44 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 148 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 148 283 (Polychromatic418967fa.accept_25_17_23_8_1_13888 42 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 283 (accept_3_3 41 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 148 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 148 283 (accept_3_3 38 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 283 (accept_3_3 35 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 283 (accept_3_3 32 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 283 (accept_3_3 29 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 283 (accept_3_3 26 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 283 (accept_3_3 23 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 148
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 283 (accept_3_3 20 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 283 (accept_3_3 17 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 283 (accept_3_3 14 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 283 (accept_3_3 11 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 283 (accept_3_3 8 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 283 (accept_3_3 5 148 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 283 (accept_3_3 2 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 148 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 147 283 (Eq.refl Bool.true) (allA_succ_of_accept 136 147 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 136 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 147 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 135 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 147 283 (accept_3_3 134 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 133 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 132 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 147 283 (accept_3_3 131 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 130 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 147 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 129 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 147 283 (accept_3_3 128 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 127 147
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 147 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 126 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 147 283 (accept_3_3 125 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 124 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 123 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 147 283 (accept_3_3 122 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 147 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 121
  147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 147 283
  (Polychromatic418967fa.accept_16_8_3_11_1_4763 120 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 147 283 (accept_3_3 119 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 118 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 147 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 117 147
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 147 283 (accept_3_3 116 147
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 115 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 114 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 147 283 (accept_3_3 113 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 147 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 111 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 147 283 (accept_3_3 110 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 147 283 (Polychromatic418967fa.accept_14_10_7_3_1_1022 108 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 283 (accept_3_3 107 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 147
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 147 283 (accept_3_3 104 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 147 283 (Polychromatic418967fa.accept_16_7_3_11_1_3682 103 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 102 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 283 (accept_3_3 101 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57
  100 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 147 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 99 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 147 283 (accept_3_3 98 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 283 (accept_3_3 95 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 147 283 (accept_3_3 92 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 147 283 (Polychromatic418967fa.accept_20_10_7_3_1_16094 90 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 283 (accept_3_3 89 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 147 283 (accept_3_3 86 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 147 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 147 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 283 (accept_3_3 83 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 283 (accept_3_3 80 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 283 (accept_3_3 77 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 75 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 283 (accept_3_3 74 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 283 (accept_3_3 71 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 283 (accept_3_3 68 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 66 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 283 (accept_3_3 65 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 283
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 283 (accept_3_3 62 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 147 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 283 (accept_3_3 59 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 283 (accept_3_3 56 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 283 (accept_3_3 53 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 283 (accept_3_3 50 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 283 (Polychromatic418967fa.accept_19_11_14_17_1_6607 49 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 283 (accept_3_3 47 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 283 (accept_3_3 44 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 283 (accept_3_3 41 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 283
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 283 (accept_3_3 38 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 283 (accept_3_3 35 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 283 (accept_3_3 32 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 283 (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 283 (accept_3_3 29 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 283
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 283 (accept_3_3 26 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 283 (accept_3_3 23 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 283 (accept_3_3 20 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 283 (accept_3_3 17 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 283 (accept_3_3 14 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 283 (Polychromatic418967fa.accept_25_13_22_8_1_4827 13 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 283 (accept_3_3 11 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 283 (accept_3_3 8 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 283 (accept_3_3 5 147 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 283 (accept_3_3 2 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 147 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 146 283 (Eq.refl Bool.true) (allA_of_3_1 138 146 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 139 145 283 (Eq.refl Bool.true) (allA_succ_of_accept 138 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 138 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 145 283 (accept_3_3 137 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  136 145 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 136 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 135 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 135 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 145 283 (accept_3_3 134 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 133 145
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 145 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 132 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 145 283 (accept_3_3 131 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 130 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 129 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 145 283 (accept_3_3 128 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 127 145
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 126 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 145 283 (accept_3_3 125 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 124 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 145 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 123 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 145 283 (accept_3_3 122 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 121 145
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 145 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 120 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 145 283 (accept_3_3 119 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 145 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 117 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 145 283 (accept_3_3 116 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 145
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 145 283 (accept_3_3 113 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 145 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 112 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 111 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 145 283 (accept_3_3 110 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 145 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 109 145
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 145 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 108 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 145 283 (accept_3_3 107 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 145 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 105 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 145 283 (accept_3_3 104 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 145 283 (Polychromatic418967fa.accept_13_12_2_10_1_2698 103
  145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 145 283 (accept_3_3 101 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 283 (accept_3_3 98 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 145 283 (accept_3_3 95 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 283 (accept_3_3 92 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 145 283 (accept_3_3 89 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 145 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 283 (accept_3_3 86 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 145 283 (accept_3_3 83 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 145 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 283 (accept_3_3 80 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 145 283 (accept_3_3 77 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 145 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 76 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 283 (accept_3_3 74 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 73 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 283 (accept_3_3 71 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 283 (accept_3_3 68 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 283 (accept_3_3 65 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 283 (accept_3_3 62 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 283 (accept_3_3 59 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 283 (accept_3_3 56 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 55 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 283 (accept_3_3 53 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 283 (accept_3_3 50 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 283 (accept_3_3 47 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 283 (accept_3_3 44 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 283 (accept_3_3 41 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 283 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 283 (accept_3_3 38 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 283 (accept_3_3 35 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 283 (accept_3_3 32 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 283 (accept_3_3 29 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 283 (accept_3_3 26 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 283 (accept_3_3 23 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 283 (accept_3_3 20 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 283 (accept_3_3 17 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 283 (accept_3_3 14 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 283 (Polychromatic418967fa.accept_24_13_1_19_1_7174 13 145 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 283 (accept_3_3 11 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 283 (accept_3_3 8 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 283 (accept_3_3 5 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 145 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 283 (accept_3_3 2 145 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 144 283 (Eq.refl Bool.true) (allA_succ_of_accept 139 144 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 139 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 138 144 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 138 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 144 283 (accept_3_3 137 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 136 144 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 136 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 144 283
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 135 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 144 283 (accept_3_3 134 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 144 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 133 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 132 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 144 283 (accept_3_3 131 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 144 283
  (Polychromatic418967fa.accept_22_20_12_19_1_15977 130 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 129 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 144 283 (accept_3_3 128 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 127 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 144 283
  (Polychromatic418967fa.accept_13_9_1_10_1_647 126 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 144 283 (accept_3_3 125 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 144 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 124 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 144 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 123 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 144 283 (accept_3_3 122 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 144 283
  (Polychromatic418967fa.accept_13_4_1_10_1_693 121 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 120 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 144 283 (accept_3_3 119 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 118 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 144 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 117 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 144 283 (accept_3_3 116 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 144 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 115 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 144 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 114 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 144 283 (accept_3_3 113 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 144 283
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 112 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 111 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 144 283 (accept_3_3 110 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 109 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 144 283
  (Polychromatic418967fa.accept_13_4_1_10_1_693 108 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 144 283 (accept_3_3 107 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 144 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 105 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 144 283 (accept_3_3 104 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 144 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 103 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 144 283
  (Polychromatic418967fa.accept_13_11_1_10_1_648 102 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 144 283 (accept_3_3 101 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 144 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 100 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 99
  144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 144 283 (accept_3_3 98
  144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 144 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 97 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 144 283 (Polychromatic418967fa.accept_27_15_9_13_1_13683 96 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 144 283 (accept_3_3 95 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 144 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 94 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 144 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 93 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 144 283 (accept_3_3 92 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 144 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 91 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 144 283 (accept_3_3 89 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 144 283 (Polychromatic418967fa.accept_25_13_19_8_1_10561 88 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 144 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 87 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 144 283 (accept_3_3 86 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 144 283 (Polychromatic418967fa.accept_19_8_11_17_1_9503 84 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 144 283 (accept_3_3 83 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 82 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 144 283
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 144 283 (accept_3_3 80 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 79 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 144 283 (accept_3_3 77 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 283
  (Polychromatic418967fa.accept_19_18_11_17_1_12083 75 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 144 283 (accept_3_3 74 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 144 283 (Polychromatic418967fa.accept_20_13_4_3_1_14612 73 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 283
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 72 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 283 (accept_3_3 71 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 144 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 283 (accept_3_3 68 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 283 (Polychromatic418967fa.accept_10_7_4_3_1_560
  67 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 283
  (Polychromatic418967fa.accept_19_9_11_17_1_9445 66 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 144 283 (accept_3_3 65 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 283 (accept_3_3 62 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 283
  (Polychromatic418967fa.accept_13_9_1_10_1_647 61 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 144 283 (Polychromatic418967fa.accept_17_9_8_11_1_1040 60 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 144 283 (accept_3_3 59 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 144 283 (Polychromatic418967fa.accept_26_6_14_23_1_17367 58 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 144 283 (accept_3_3 56 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 144 283 (Polychromatic418967fa.accept_20_14_4_3_1_2006 54 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 283 (accept_3_3 53 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 52 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 283
  (Polychromatic418967fa.accept_19_13_11_17_1_5152 51 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 144 283 (accept_3_3 50 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 283 (accept_3_3 47 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 283
  (Polychromatic418967fa.accept_19_8_11_17_1_9503 46 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 283 (Polychromatic418967fa.accept_21_3_18_10_1_10020 45 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 283 (accept_3_3 44 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 283
  (Polychromatic418967fa.accept_19_4_11_17_1_9505 42 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 144 283 (accept_3_3 41 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 144 283 (Polychromatic418967fa.accept_23_17_6_7_1_17366 40 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539
  39 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 283 (accept_3_3 38
  144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 37 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 283 (accept_3_3 35 144 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 144 283 (accept_3_3 32 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 144 283 (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 144 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 30 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 283 (accept_3_3 29 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 283 (Polychromatic418967fa.accept_19_9_11_17_1_9445 28 144
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 144 283 (accept_3_3 26 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 144 283 (Polychromatic418967fa.accept_19_6_11_17_1_2611 25 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 144 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 283 (accept_3_3 23 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 144 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 283
  (Polychromatic418967fa.accept_14_7_4_3_1_488 21 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 144 283 (accept_3_3 20 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 144 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 283 (accept_3_3 17 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 283 (Polychromatic418967fa.accept_22_16_12_19_1_11328 16
  144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 283 (accept_3_3 14 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 283 (Polychromatic418967fa.accept_25_12_19_8_1_17365 12 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 283 (accept_3_3 11 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 283 (Polychromatic418967fa.accept_25_10_19_8_1_12163 10
  144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 283
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 283 (accept_3_3 8 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 283 (accept_3_3 5 144 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 144 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 283 (accept_3_3 2 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 141 143 283 (Eq.refl Bool.true) (allA_of_3_1 141 143 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 142 283 (allA_succ_of_accept 141 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 141 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 140 142 283 (accept_3_3 140 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 142 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 139 142
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 142 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 138 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 142 283 (accept_3_3 137 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  136 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 136 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 135 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 142 283 (accept_3_3 134 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 133 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 133 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 142 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 132 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 142 283 (accept_3_3 131 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 142 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 130 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 129 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 142 283 (accept_3_3 128 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 127 142 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 127 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 142 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 126 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 142 283 (accept_3_3 125 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 142 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 124 142 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 123 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 142 283 (accept_3_3 122 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  121 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 142 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 120 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 142 283 (accept_3_3 119 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 142 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 118 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 142 283 (accept_3_3 116 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 142 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 115 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 142 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 114 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 142 283 (accept_3_3 113 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 142 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 112 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 142 283 (accept_3_3 110 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 142 283
  (Polychromatic418967fa.accept_11_9_10_8_1_444 108 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 142 283 (accept_3_3 107 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 142 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 142 283 (accept_3_3 104 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 142 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 142 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 142 283 (accept_3_3 101 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 142 283 (accept_3_3 98 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 142 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 142 283 (accept_3_3 95 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 142 283 (Polychromatic418967fa.accept_29_7_26_22_1_17364 94 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 142 283 (accept_3_3 92 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 142 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 90 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 142 283 (accept_3_3 89 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 142 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 142 283 (accept_3_3 86 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 142 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 142 283 (accept_3_3 83 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 142 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 142 283 (accept_3_3 80 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 142 283 (Polychromatic418967fa.accept_20_19_2_3_1_4486 79 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 142 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 142 283 (accept_3_3 77 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 142 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 142 283 (accept_3_3 74 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 142 283
  (Polychromatic418967fa.accept_13_7_12_10_1_640 72 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 142 283 (accept_3_3 71 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 142 283 (Polychromatic418967fa.accept_19_13_9_17_1_8070 70 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 283 (accept_3_3 68 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 142 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 283 (accept_3_3 65 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 283 (accept_3_3 62 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 283 (accept_3_3 59 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 58 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 283 (accept_3_3 56 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 283 (accept_3_3 53 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 283 (accept_3_3 50 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 283 (accept_3_3 47 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 283 (accept_3_3 44 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 283 (accept_3_3 41 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 283 (accept_3_3 38 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 283 (accept_3_3 35 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 283 (accept_3_3 32 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 283 (accept_3_3 29 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 283 (accept_3_3 26 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 283 (accept_3_3 23 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 283 (accept_3_3 20 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 283
  (Polychromatic418967fa.accept_20_18_2_3_1_3169 18 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 283 (accept_3_3 17 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 283 (accept_3_3 14 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 283 (accept_3_3 11 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 283 (accept_3_3 8 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 283 (accept_3_3 5 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 142 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 283 (accept_3_3 2 142 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 141 283 (allA_succ_of_accept 140 141 283 (accept_3_3 140 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 139 141 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 139 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  138 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 141 283 (accept_3_3
  137 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 141 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 136 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 135 141 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 141 283 (accept_3_3 134 141 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 141 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 133 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 141 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 132 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 141 283 (accept_3_3 131 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 130 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 141 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 129 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 141 283 (accept_3_3 128 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 127 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 126 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 141 283 (accept_3_3 125 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 124 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 123 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 141 283 (accept_3_3 122 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 121 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 120 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 141 283 (accept_3_3 119 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 141 283 (accept_3_3 116 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 115 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 141 283 (accept_3_3 113 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 141 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 141 283 (accept_3_3 110 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 108 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 141 283 (accept_3_3 107 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 141 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 105 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 141 283 (accept_3_3 104 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 141 283 (accept_3_3 101 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 141 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 283 (accept_3_3 98 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 96 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 141 283 (accept_3_3 95 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 283 (accept_3_3 92 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 283 (accept_3_3 89 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 283 (accept_3_3 86 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 283 (Polychromatic418967fa.accept_19_9_8_17_1_8053 85 141
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 283 (accept_3_3 83 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 283 (accept_3_3 80 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 283 (accept_3_3 77 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 283 (accept_3_3 74 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 283 (accept_3_3 71 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 283 (accept_3_3 68 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 283 (accept_3_3 65 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 283 (accept_3_3 62 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 283 (accept_3_3 59 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 283 (accept_3_3 56 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 283 (accept_3_3 53 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 283 (accept_3_3 50 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 283 (accept_3_3 47 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 283 (Polychromatic418967fa.accept_20_5_1_3_1_5983 45 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 283 (accept_3_3 44 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 283 (accept_3_3 41 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 283 (accept_3_3 38 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 283
  (Polychromatic418967fa.accept_22_14_9_19_1_17363 36 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 283 (accept_3_3 35 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 283 (accept_3_3 32 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 283
  (Polychromatic418967fa.accept_25_6_16_8_1_15750 31 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 283 (accept_3_3 29 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 283 (accept_3_3 26 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 283 (accept_3_3 23 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 283 (accept_3_3 20 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 283 (accept_3_3 17 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 283 (accept_3_3 14 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 283 (Polychromatic418967fa.accept_20_13_1_3_1_11831 13 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 283 (accept_3_3 11 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 283 (accept_3_3 8 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 283 (accept_3_3 5 141 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 283 (accept_3_3 2 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 141 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 283 (allA_of_3_1 140 140 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 139 283
  (allA_succ_of_accept 138 139 283 (Polychromatic418967fa.accept_17_2_3_11_1_2919 138 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 139 283 (accept_3_3 137 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 136 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 136 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 139 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 135 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 139 283 (accept_3_3 134 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 139 283 (Polychromatic418967fa.accept_17_14_3_11_1_11591 133 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 132 139 283 (Polychromatic418967fa.accept_19_18_6_17_1_8078 132 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 139 283 (accept_3_3 131 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271
  130 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 139 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 129 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 139 283 (accept_3_3 128 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 139 283 (Polychromatic418967fa.accept_19_13_6_17_1_12101 127 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935
  126 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 139 283 (accept_3_3
  125 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 139 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 124 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 123 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 139 283 (accept_3_3 122 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 121 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 139 283
  (Polychromatic418967fa.accept_22_10_7_19_1_17362 120 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 139 283 (accept_3_3 119 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 139 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 118 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 139 283
  (Polychromatic418967fa.accept_19_3_6_17_1_6579 117 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 139 283 (accept_3_3 116 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 139 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 115 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100
  114 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 139 283 (accept_3_3
  113 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 139 283
  (Polychromatic418967fa.accept_17_10_3_11_1_6482 112 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 139 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 111 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 139 283 (accept_3_3 110 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 139 283
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 108 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 139 283 (accept_3_3 107 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 106 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 105 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 139 283 (accept_3_3 104 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 139 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 103 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 283 (accept_3_3 101 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 283
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 99 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 283 (accept_3_3 98 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 97 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 96 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 283 (accept_3_3 95 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 94 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 283 (accept_3_3 92 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 283 (Polychromatic418967fa.accept_21_7_13_10_1_8604 91 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 90 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 283 (accept_3_3 89 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 283
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 87 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 283 (accept_3_3 86 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 85 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 283 (accept_3_3 83 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 283 (Polychromatic418967fa.accept_17_14_3_11_1_11591 82
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 283 (accept_3_3 80 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 283 (Polychromatic418967fa.accept_17_10_3_11_1_6482 78 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 283 (accept_3_3 77 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 283
  (Polychromatic418967fa.accept_19_18_6_17_1_8078 75 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 139 283 (accept_3_3 74 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 139 283 (Polychromatic418967fa.accept_25_23_14_8_1_17361 73 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100
  72 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 283 (accept_3_3 71
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 139 283 (Polychromatic418967fa.accept_15_9_4_13_1_4482 69 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 283 (accept_3_3 68 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935
  66 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 283 (accept_3_3 65
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 139 283 (Polychromatic418967fa.accept_23_17_1_7_1_17360 63 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 283 (accept_3_3 62 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 283 (Polychromatic418967fa.accept_17_10_3_11_1_6482 61 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 283 (accept_3_3 59 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 283 (Polychromatic418967fa.accept_22_13_7_19_1_15931 57 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 283 (accept_3_3 56 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 283 (accept_3_3 53 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 52 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 283 (accept_3_3 50 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 283 (Polychromatic418967fa.accept_19_11_6_17_1_9455 49 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 283 (accept_3_3 47 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 283 (accept_3_3 44 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 283 (Polychromatic418967fa.accept_17_9_3_11_1_3983 43 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 283
  (Polychromatic418967fa.accept_19_4_6_17_1_12062 42 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 139 283 (accept_3_3 41 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 139 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 283 (accept_3_3 38 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 283
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 283 (accept_3_3 35 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 283 (Polychromatic418967fa.accept_27_6_4_13_1_17359 33 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 283 (accept_3_3 32 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 283 (Polychromatic418967fa.accept_17_14_3_11_1_11591 31
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 283 (accept_3_3 29 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 283 (Polychromatic418967fa.accept_19_9_6_17_1_3880 28 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 283 (accept_3_3 26 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 283 (accept_3_3 23 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 283 (Polychromatic418967fa.accept_19_3_6_17_1_6579 22 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 21 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 283 (accept_3_3 20 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 283 (accept_3_3 17 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 283 (accept_3_3 14 139 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 283 (Polychromatic418967fa.accept_19_13_6_17_1_12101 13
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 139 283 (accept_3_3 11 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 139 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 283 (accept_3_3 8 139
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 283
  (Polychromatic418967fa.accept_21_7_13_10_1_8604 7 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 139 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 283 (accept_3_3 5 139 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 139 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 283 (Polychromatic418967fa.accept_19_3_6_17_1_6579
  3 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 283 (accept_3_3 2
  139 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 283
  (Polychromatic418967fa.accept_13_1_9_10_1_625 1 139 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 139
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 138 283 (allA_succ_of_accept 137 138 283 (accept_3_3 137 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 136 138 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 135 138
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 138 283 (accept_3_3 134 138
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 133 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 132 138 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 138 283 (accept_3_3 131 138 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 138 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 130 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 129 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 138 283 (accept_3_3 128 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 127 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 138 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 126 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 138 283 (accept_3_3 125 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 124 138
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 138 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 123 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 138 283 (accept_3_3 122 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 120 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 138 283 (accept_3_3 119 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 118 138
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 138 283 (accept_3_3 116 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 115 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 138 283 (accept_3_3 113 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 138 283 (Polychromatic418967fa.accept_22_2_6_19_1_6438 112
  138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 138 283
  (Polychromatic418967fa.accept_10_1_8_3_1_947 111 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 138 283 (accept_3_3 110 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 138 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 108 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 138 283 (accept_3_3 107 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 138
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 138 283 (accept_3_3 104 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 138 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 103 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 138 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 102 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 138 283 (accept_3_3 101 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98
  100 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 138 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 138 283 (accept_3_3 98 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 138 283 (accept_3_3 95 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 138 283 (Polychromatic418967fa.accept_17_9_2_11_1_4042 94 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 138 283 (accept_3_3 92 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 138 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 90 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 138 283 (accept_3_3 89 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 138 283 (accept_3_3 86 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 138 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 84 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 138 283 (accept_3_3 83 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 138 283 (accept_3_3 80 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 138 283 (accept_3_3 77 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 283
  (Polychromatic418967fa.accept_10_5_8_3_1_229 75 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 138 283 (accept_3_3 74 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 138 283 (accept_3_3 71 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 138 283 (accept_3_3 68 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 138 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 138 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 138 283 (accept_3_3 65 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 283
  (Polychromatic418967fa.accept_13_11_8_10_1_676 63 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 138 283 (accept_3_3 62 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 138 283 (accept_3_3 59 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 138 283 (accept_3_3 56 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 138 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 138 283 (accept_3_3 53 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 138 283 (accept_3_3 50 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 138 283 (Polychromatic418967fa.accept_20_8_18_3_1_10560 48 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 283 (accept_3_3 47 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 138 283 (accept_3_3 44 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 283 (accept_3_3 41 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 138 283 (accept_3_3 38 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 283 (accept_3_3 35 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 138 283 (accept_3_3 32 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 138 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 283 (accept_3_3 29 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 283 (accept_3_3 26 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 283 (accept_3_3 23 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 283 (Polychromatic418967fa.accept_7_1_5_3_1_268
  22 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 283 (accept_3_3 20 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 283 (accept_3_3 17 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 283 (accept_3_3 14 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 283 (accept_3_3 11 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 138 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 283 (accept_3_3 8 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 283 (accept_3_3 5 138 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 138 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 283 (accept_3_3 2 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 283 (allA_of_3_1 137 137 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 136 283
  (allA_succ_of_accept 135 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 135 136 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 136 283 (accept_3_3 134 136 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 133 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 132 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 136 283 (accept_3_3 131 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 130 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 129 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 136 283 (accept_3_3 128 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 127 136 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 127 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 136 283
  (Polychromatic418967fa.accept_13_9_6_10_1_666 126 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 136 283 (accept_3_3 125 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 124 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 123 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 136 283 (accept_3_3 122 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 121 136 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 121 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 120 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 136 283 (accept_3_3 119 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 136 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 118 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 117 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 136 283 (accept_3_3 116 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 114 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 136 283 (accept_3_3 113 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 136 283 (Polychromatic418967fa.accept_18_4_10_13_1_5883 112 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 136 283 (accept_3_3 110 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 136 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 109 136
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 136 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 136 283 (accept_3_3 107 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 136 283 (accept_3_3 104 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 136 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 103 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 102 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 136 283 (accept_3_3 101 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 136 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 100 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 136 283 (accept_3_3 98 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 136 283 (accept_3_3 95 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 136 283 (accept_3_3 92 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 136 283 (Polychromatic418967fa.accept_14_7_10_3_1_1034 91 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 136 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 90 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 136 283 (accept_3_3 89 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 136 283 (accept_3_3 86 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 136 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 85 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 136 283 (accept_3_3 83 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 136 283 (accept_3_3 80 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 136 283 (accept_3_3 77 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 136 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 76 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 136 283 (accept_3_3 74 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 136 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 73 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 136 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 72 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 136 283 (accept_3_3 71 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 136 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 283 (accept_3_3 68 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 283 (Polychromatic418967fa.accept_10_7_6_3_1_927
  67 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 283 (accept_3_3 65 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 64 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 283 (accept_3_3 62 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 283 (accept_3_3 59 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 283 (accept_3_3 56 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 283
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 283 (accept_3_3 53 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 283 (accept_3_3 50 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 283 (accept_3_3 47 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 283 (accept_3_3 44 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 283 (accept_3_3 41 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 283 (accept_3_3 38 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 283
  (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 283 (accept_3_3 35 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 283 (accept_3_3 32 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 283 (accept_3_3 29 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 283 (accept_3_3 26 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 283 (accept_3_3 23 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 283 (accept_3_3 20 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 283 (accept_3_3 17 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 283 (accept_3_3 14 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 136 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 283 (accept_3_3 11 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 283 (accept_3_3 8 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 283 (accept_3_3 5 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 136 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 283 (accept_3_3 2 136 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 136 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 135 283 (allA_succ_of_accept 134 135 283 (accept_3_3 134 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 135 283 (Polychromatic418967fa.accept_16_5_7_11_1_2664 133 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107
  132 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 283 (accept_3_3
  131 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 135 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 130 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 135 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 129 135 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 135 283 (accept_3_3 128 135 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 127 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 135 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 126 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 135 283 (accept_3_3 125 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 124 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 135 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 123 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 135 283 (accept_3_3 122 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 121
  135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 120 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 135 283 (accept_3_3 119 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 118 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 117 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 283 (accept_3_3 116 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 115 135
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 283
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 114 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 135 283 (accept_3_3 113 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 135 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 111 135
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 135 283 (accept_3_3 110 135
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 283
  (Polychromatic418967fa.accept_19_14_2_17_1_678 109 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 135 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 283 (accept_3_3 107 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 135
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 135 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 105 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 135 283 (accept_3_3 104 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 135 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 102 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 283 (accept_3_3 101 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 135
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 135 283 (accept_3_3 98 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 283 (accept_3_3 95 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 93 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 283 (accept_3_3 92 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 135 283 (Polychromatic418967fa.accept_19_15_2_17_1_5163 91 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 283 (accept_3_3 89 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 87 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 135 283 (accept_3_3 86 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 135 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 283 (accept_3_3 83 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 135 283 (accept_3_3 80 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 135 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 79 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 283 (accept_3_3 77 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 283 (accept_3_3 74 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 283 (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 283 (accept_3_3 71 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 283 (accept_3_3 68 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 283 (Polychromatic418967fa.accept_16_2_7_11_1_1698 66 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 283 (accept_3_3 65 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 283
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 63 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 283 (accept_3_3 62 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 135 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 283 (accept_3_3 59 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 283 (accept_3_3 56 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 283 (accept_3_3 53 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 283
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 51 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 135 283 (accept_3_3 50 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 135 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 283 (accept_3_3 47 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 283 (accept_3_3 44 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 283 (accept_3_3 41 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 283 (accept_3_3 38 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 283 (accept_3_3 35 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 283 (accept_3_3 32 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 283 (accept_3_3 29 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 283 (accept_3_3 26 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 283 (Polychromatic418967fa.accept_20_5_15_3_1_4516 25 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 283 (Polychromatic418967fa.accept_18_6_9_13_1_3320 24 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 283 (accept_3_3 23 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 283 (accept_3_3 20 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 283 (accept_3_3 17 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 283 (accept_3_3 14 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 283 (accept_3_3 11 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 283 (accept_3_3 8 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 283 (accept_3_3 5 135 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 283
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 283 (accept_3_3 2 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 283 (allA_of_3_1 134 134 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 133 283
  (allA_succ_of_accept 132 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 132 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 133 283 (accept_3_3 131 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 130 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 129 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 133 283 (accept_3_3 128 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 127 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 133 283 (accept_3_3 125 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 133 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 124 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 133 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 123 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 133 283 (accept_3_3 122 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 133 283 (Polychromatic418967fa.accept_16_9_5_11_1_3776 121 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 120 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 133 283 (accept_3_3 119 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 283
  (Polychromatic418967fa.accept_23_2_18_7_1_11086 117 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 133 283 (accept_3_3 116 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 133 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 115 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 133 283 (accept_3_3
  113 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 133 283
  (Polychromatic418967fa.accept_18_4_7_13_1_3303 112 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 111 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 133 283 (accept_3_3 110 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 133 283
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 108 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 133 283 (accept_3_3 107 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 133 283 (accept_3_3 104 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 133 283
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 103 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 283 (accept_3_3 101 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 283
  (Polychromatic418967fa.accept_21_15_7_10_1_8610 99 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 133 283 (accept_3_3 98 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 133 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 97 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 283 (accept_3_3 95 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 93 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 283 (accept_3_3 92 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 283 (accept_3_3 89 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 88 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 283 (accept_3_3 86 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 85 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 283 (accept_3_3 83 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 283
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 283 (accept_3_3 80 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 283 (Polychromatic418967fa.accept_21_16_7_10_1_8601 79 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 283 (accept_3_3 77 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 76 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 283 (accept_3_3 74 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 283 (accept_3_3 71 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 283 (accept_3_3 68 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 67 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 283 (accept_3_3 65 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 283
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 133 283 (accept_3_3 62 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 133 283 (Polychromatic418967fa.accept_20_1_13_3_1_11838 61 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212
  60 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 283 (accept_3_3 59
  133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 283 (accept_3_3 56 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 283 (accept_3_3 53
  133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 283
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 283 (accept_3_3 50 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 133 283 (Polychromatic418967fa.accept_24_1_13_19_1_2191 49 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 283 (accept_3_3 47 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 283 (accept_3_3 44 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 283 (Polychromatic418967fa.accept_21_1_7_10_1_2596 43 133
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 283 (accept_3_3 41 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 283 (Polychromatic418967fa.accept_16_8_5_11_1_4776 40 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 283 (accept_3_3 38 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 283
  (Polychromatic418967fa.accept_20_16_13_3_1_5974 36 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 133 283 (accept_3_3 35 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 283 (accept_3_3 32 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 283
  (Polychromatic418967fa.accept_20_11_13_3_1_7409 31 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 283 (accept_3_3 29 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 283
  (Polychromatic418967fa.accept_26_1_3_23_1_10056 27 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 133 283 (accept_3_3 26 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 133 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 133 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 283 (accept_3_3 23 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 283 (accept_3_3 20 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 283 (accept_3_3 17 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 283 (Polychromatic418967fa.accept_17_16_14_11_1_7836 16 133 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 283 (accept_3_3 14 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 283 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 283 (accept_3_3 11 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 283
  (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 283 (accept_3_3 8 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 283 (accept_3_3 5 133 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 133 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 283 (accept_3_3 2 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 132 283 (allA_succ_of_accept 131 132 283 (accept_3_3 131 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 130 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 129 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 132 283 (accept_3_3 128 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 132 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 127 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 132 283 (Polychromatic418967fa.accept_17_7_13_11_1_2895 126 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 132 283 (accept_3_3 125 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 124 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 124 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 132 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 123 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 132 283 (accept_3_3 122 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 121 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 120 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 132 283 (accept_3_3 119 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 118 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 132 283
  (Polychromatic418967fa.accept_17_15_13_11_1_4031 117 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 132 283 (accept_3_3 116 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 115 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 114 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 132 283 (accept_3_3 113 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 132 283
  (Polychromatic418967fa.accept_13_8_2_10_1_652 112 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 132 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 111 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 132 283 (accept_3_3 110 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 132 283
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 108 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 132 283 (accept_3_3 107 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 132 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 105 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 132 283 (accept_3_3 104 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 132 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 132 283 (accept_3_3 101 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 132 283
  (Polychromatic418967fa.accept_13_8_2_10_1_652 99 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 132 283 (accept_3_3 98 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 132 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 96 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 132 283 (accept_3_3 95 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 132 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 94 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 132 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 132 283 (accept_3_3 92 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 132 283 (Polychromatic418967fa.accept_13_12_2_10_1_2698 90 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 132 283 (accept_3_3 89 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 87 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 132 283 (accept_3_3 86 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 132 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 85 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 283 (accept_3_3 83 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 132 283 (accept_3_3 80 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 132 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 78 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 283 (accept_3_3 77 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 76 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 132 283 (accept_3_3 74 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 283 (accept_3_3 71 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 283
  (Polychromatic418967fa.accept_19_12_18_17_1_8075 69 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 132 283 (accept_3_3 68 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 283 (accept_3_3 65 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 64
  132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 63 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 132 283 (accept_3_3 62 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 283 (accept_3_3 59 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 132 283 (accept_3_3 56 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 132 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 132 283 (Polychromatic418967fa.accept_16_6_4_11_1_1719 54 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 283 (accept_3_3 53 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 132 283 (accept_3_3 50 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 132 283 (Polychromatic418967fa.accept_17_15_13_11_1_4031 49 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 283 (accept_3_3 47 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 283
  (Polychromatic418967fa.accept_10_5_2_3_1_239 45 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 132 283 (accept_3_3 44 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 132 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 283 (accept_3_3 41 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40
  132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 132 283 (accept_3_3 38 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 132 283 (Polychromatic418967fa.accept_21_15_6_10_1_10016 36 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 283 (accept_3_3 35 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 132 283 (accept_3_3 32 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 132 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 283 (accept_3_3 29 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28
  132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 283
  (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 132 283 (accept_3_3 26 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 132 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 283 (accept_3_3 23 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 283 (Polychromatic418967fa.accept_16_6_4_11_1_1719 22 132
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 283 (accept_3_3 20 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 283 (accept_3_3 17 132 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 132 283 (accept_3_3 14 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 132 283 (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 283 (accept_3_3 11 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 132 283 (accept_3_3 8 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  132 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 132 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 283 (accept_3_3 5 132 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 132 283 (accept_3_3 2 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  132 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 132 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 283 (allA_of_3_1 131 131 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 130 283
  (allA_succ_of_accept 129 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 129 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 130 283 (accept_3_3 128 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 127 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 130 283
  (Polychromatic418967fa.accept_25_1_5_8_1_13889 126 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 130 283 (accept_3_3 125 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 124 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 130 283 (Polychromatic418967fa.accept_6_3_4_1_1_8
  123 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 130 283 (accept_3_3
  122 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 121 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 120 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 130 283 (accept_3_3 119 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 118 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 130 283 (accept_3_3 116 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 130 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 115 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 130 283 (Polychromatic418967fa.accept_23_22_15_7_1_17358 114 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 130 283 (accept_3_3 113 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 130 283
  (Polychromatic418967fa.accept_12_4_10_7_1_149 112 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 130 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 130 283 (accept_3_3 110 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 130 283
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 108 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 130 283 (accept_3_3 107 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 130 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 130 283 (accept_3_3 104 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 130 283
  (Polychromatic418967fa.accept_16_7_2_11_1_931 103 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 130 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 102 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 130 283 (accept_3_3 101 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 130 283 (accept_3_3 98 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 130 283 (Polychromatic418967fa.accept_19_1_16_17_1_3864 96 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 130 283 (accept_3_3 95 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 130 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 94 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 130 283 (accept_3_3 92 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 130 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 91 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 130 283 (accept_3_3 89 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 130 283 (accept_3_3 86 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 130 283 (Polychromatic418967fa.accept_19_8_16_17_1_6552 84 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 130 283 (accept_3_3 83 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 130 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 82 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 130 283 (accept_3_3 80 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 130 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 79 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 130 283 (accept_3_3 77 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 130 283 (accept_3_3 74 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 130 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 72 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 283 (accept_3_3 71 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 130 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 70 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 283 (accept_3_3 68 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 283 (Polychromatic418967fa.accept_20_7_10_3_1_949 67 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 130 283 (Polychromatic418967fa.accept_23_20_15_7_1_15875 66 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 130 283 (accept_3_3 65 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 283 (accept_3_3 62 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 130 283 (Polychromatic418967fa.accept_19_3_16_17_1_3826 60 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 130 283 (accept_3_3 59 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 283 (Polychromatic418967fa.accept_19_1_16_17_1_3864 58 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 283 (accept_3_3 56 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 283 (accept_3_3 53 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 283 (accept_3_3 50 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 283 (accept_3_3 47 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 283 (accept_3_3 44 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 42 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 283 (accept_3_3 41 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 283 (accept_3_3 38 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 283 (accept_3_3 35 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 283 (accept_3_3 32 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 283 (Polychromatic418967fa.accept_22_8_20_19_1_8153 30 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 283 (accept_3_3 29 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 283 (accept_3_3 26 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 283 (Polychromatic418967fa.accept_22_2_20_19_1_9752 24 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 283 (accept_3_3 23 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 283 (accept_3_3 20 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 283 (accept_3_3 17 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 283 (accept_3_3 14 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 283 (accept_3_3 11 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 130
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 283 (accept_3_3 8 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 283 (accept_3_3 5 130 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 283 (accept_3_3 2 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 129 283 (allA_succ_of_accept 128 129 283 (accept_3_3 128 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 127 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 129
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 283 (accept_3_3 125 129
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 129 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 124 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 129 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 123 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 129 283 (accept_3_3 122 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 129 283 (Polychromatic418967fa.accept_19_7_15_17_1_5198 121 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 283
  (Polychromatic418967fa.accept_17_1_10_11_1_2943 120 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 129 283 (accept_3_3 119 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 129 283 (Polychromatic418967fa.accept_18_9_3_13_1_5905 117
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 129 283 (accept_3_3 116
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 115 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 283 (accept_3_3 113 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 111 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 129 283 (accept_3_3 110 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 129 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 108 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 283 (accept_3_3 107 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 129
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 129 283 (accept_3_3 104 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 129 283 (Polychromatic418967fa.accept_17_1_10_11_1_2943 103 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 283 (accept_3_3 101 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 129
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 99 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 129 283 (accept_3_3 98 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 129 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 283 (accept_3_3 95 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 283
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 93 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 283 (accept_3_3 92 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 283 (accept_3_3 89 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 283 (accept_3_3 86 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 85 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 283 (accept_3_3 83 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 283
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 81 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 283 (accept_3_3 80 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 283 (accept_3_3 77 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 283 (accept_3_3 74 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 72 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 283 (accept_3_3 71 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 283 (accept_3_3 68 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 283 (accept_3_3 65 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 283 (accept_3_3 62 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 283 (accept_3_3 59 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 283
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 57 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 283 (accept_3_3 56 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 283 (accept_3_3 53 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 283 (accept_3_3 50 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 49 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 283 (accept_3_3 47 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 283
  (Polychromatic418967fa.accept_13_6_12_10_1_690 45 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 283 (accept_3_3 44 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 283 (accept_3_3 41 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 283 (accept_3_3 38 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 283 (accept_3_3 35 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 283 (accept_3_3 32 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 31 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 283 (accept_3_3 29 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 283 (accept_3_3 26 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 283 (accept_3_3 23 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 283
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 283 (accept_3_3 20 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 129 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 283 (accept_3_3 17 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 283 (accept_3_3 14 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 283 (Polychromatic418967fa.accept_19_13_15_17_1_5199 13 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 283 (Polychromatic418967fa.accept_16_12_1_11_1_5958 12 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 283 (accept_3_3 11 129 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 283 (accept_3_3 8 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 283 (accept_3_3 5 129 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 283 (accept_3_3 2 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 129 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 283 (allA_of_3_1 128 128 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 127 283
  (allA_succ_of_accept 126 127 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 126 127 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 283 (accept_3_3 125 127 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 124 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 123 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 127 283 (accept_3_3 122 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 121 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 127 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 120 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 127 283 (accept_3_3 119 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 118
  127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 117 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 283 (accept_3_3 116 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 283 (accept_3_3 113 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 283 (Polychromatic418967fa.accept_21_7_1_10_1_8571 112
  127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 111 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 283 (accept_3_3 110 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 283 (accept_3_3 107 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 127
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 283 (accept_3_3 104 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 283 (accept_3_3 101 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 127
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 283
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 99 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 283 (accept_3_3 98 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 283 (accept_3_3 95 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 94 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 283 (accept_3_3 92 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 91 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 283 (Polychromatic418967fa.accept_16_10_15_11_1_3785 90 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 283 (accept_3_3 89 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 283 (accept_3_3 86 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 283 (accept_3_3 83 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 283 (accept_3_3 80 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 283 (accept_3_3 77 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 283 (accept_3_3 74 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 283 (Polychromatic418967fa.accept_19_16_13_17_1_12066 73 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 283 (accept_3_3 71 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 69 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 283 (accept_3_3 68 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 283 (accept_3_3 65 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 283
  (Polychromatic418967fa.accept_19_6_13_17_1_8015 63 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 127 283 (accept_3_3 62 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 127 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 283 (accept_3_3 59 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  58 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 283 (accept_3_3 56 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 283 (accept_3_3 53 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 283 (accept_3_3 50 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 283 (Polychromatic418967fa.accept_16_1_15_11_1_356 49 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 283 (accept_3_3 47 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 283 (accept_3_3 44 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 283 (accept_3_3 41 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 283 (accept_3_3 38 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 283 (accept_3_3 35 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 283 (accept_3_3 32 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 283 (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 283 (accept_3_3 29 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 283
  (Polychromatic418967fa.accept_22_5_17_19_1_12866 27 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 127 283 (accept_3_3 26 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 283 (accept_3_3 23 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 283
  (Polychromatic418967fa.accept_24_22_7_19_1_12514 22 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 283 (accept_3_3 20 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 283 (accept_3_3 17 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 283 (accept_3_3 14 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 283 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 283 (accept_3_3 11 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 283 (Polychromatic418967fa.accept_16_10_15_11_1_3785 10 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 283 (accept_3_3 8 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 283 (accept_3_3 5 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 283 (accept_3_3 2 127 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 283 (Polychromatic418967fa.accept_16_1_15_11_1_356 1 127 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 283 (allA_succ_of_accept 125 126 283 (accept_3_3 125 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 126 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 124 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 126 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 123 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 126 283 (accept_3_3 122 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 126 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 121 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 126 283 (Polychromatic418967fa.accept_17_1_7_11_1_2892 120 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 126 283 (accept_3_3 119 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 118 126 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 118 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 126 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 126 283 (accept_3_3 116 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 126 283 (Polychromatic418967fa.accept_16_3_14_11_1_2654 115 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 126 283 (Polychromatic418967fa.accept_22_4_16_19_1_12881 114 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 126 283 (accept_3_3 113 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 126 283 (Polychromatic418967fa.accept_11_2_5_8_1_470
  112 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 126 283
  (Polychromatic418967fa.accept_22_1_16_19_1_6445 111 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 126 283 (accept_3_3 110 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 126 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 126 283 (accept_3_3 107 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 126 283
  (Polychromatic418967fa.accept_23_14_11_7_1_9410 106 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 126 283 (accept_3_3 104 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 103 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 126 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 102 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 126 283 (accept_3_3 101 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 126 283 (Polychromatic418967fa.accept_19_5_12_17_1_8089 100 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 99 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 126 283 (accept_3_3 98 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 126 283
  (Polychromatic418967fa.accept_22_8_16_19_1_9787 96 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 126 283 (accept_3_3 95 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 126 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 94 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 126 283 (accept_3_3 92 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 126 283 (Polychromatic418967fa.accept_11_3_5_8_1_458
  91 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 126 283
  (Polychromatic418967fa.accept_11_2_5_8_1_470 90 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 126 283 (accept_3_3 89 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 126 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 126 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 87 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 283 (accept_3_3 86 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 126 283
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 84 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 126 283 (accept_3_3 83 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 126 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 82 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 283 (accept_3_3 80 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 79 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 126 283 (accept_3_3 77 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 126 283 (Polychromatic418967fa.accept_27_22_18_13_1_17357 76 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 283 (Polychromatic418967fa.accept_19_18_12_17_1_8026 75 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 283 (accept_3_3 74 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 283
  (Polychromatic418967fa.accept_19_15_12_17_1_5195 72 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 126 283 (accept_3_3 71 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 126 283 (Polychromatic418967fa.accept_22_4_16_19_1_12881 70 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 283 (accept_3_3 68
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 283
  (Polychromatic418967fa.accept_10_7_6_3_1_927 67 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 126 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 66 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 283 (accept_3_3 65 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 126 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 64 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 283
  (Polychromatic418967fa.accept_19_6_12_17_1_12050 63 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 126 283 (accept_3_3 62 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 283 (Polychromatic418967fa.accept_19_3_12_17_1_6585 60 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 283 (accept_3_3 59 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 283 (accept_3_3 56 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 126 283 (Polychromatic418967fa.accept_23_9_11_7_1_17348 55 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 283
  (Polychromatic418967fa.accept_28_26_14_3_1_17356 54 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 283 (accept_3_3 53 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 126 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 52 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 283 (accept_3_3 50 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  49 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 126 283 (accept_3_3 47 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 126 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 283 (accept_3_3 44 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 283 (Polychromatic418967fa.accept_19_5_12_17_1_8089 43 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 283
  (Polychromatic418967fa.accept_23_19_11_7_1_7741 42 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 126 283 (accept_3_3 41 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 283 (accept_3_3 38 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 126 283 (accept_3_3 35 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 126 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 283 (accept_3_3 32 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 283 (Polychromatic418967fa.accept_25_6_1_8_1_17340 31 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 283
  (Polychromatic418967fa.accept_17_13_7_11_1_3985 30 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 283 (accept_3_3 29 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 283 (accept_3_3 26 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  25 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 283
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 283 (accept_3_3 23 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 283 (accept_3_3 20 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 126 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 283 (accept_3_3 17 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 283 (Polychromatic418967fa.accept_23_16_11_7_1_15890 16 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 283 (Polychromatic418967fa.accept_19_15_12_17_1_5195 15 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 283 (accept_3_3 14 126 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 283 (accept_3_3 11 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 283 (Polychromatic418967fa.accept_19_10_12_17_1_1506 10 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 283 (accept_3_3 8 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 283
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 126 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 283 (accept_3_3 5 126 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 126 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 126 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 283 (accept_3_3 2 126
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 126 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 283 (allA_of_3_1 125 125 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 124 283
  (allA_succ_of_accept 123 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 123 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 124 283 (accept_3_3 122 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 121 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 124 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 120 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 124 283 (accept_3_3 119 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 118 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 117 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 124 283 (accept_3_3 116 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 124 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 115 124 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 124 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 114 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 124 283 (accept_3_3 113 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 124 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 112 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 124 283 (accept_3_3 110 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 124
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 124 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 108 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 124 283 (accept_3_3 107 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 124 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 124 283 (accept_3_3 104 124 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 124 283 (Polychromatic418967fa.accept_8_7_4_3_1_156
  103 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 124 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 124 283 (accept_3_3 101 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 124 283 (accept_3_3 98 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 124 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 97 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 124 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 124 283 (accept_3_3 95 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 124 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 94 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 124 283 (accept_3_3 92 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 124 283
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 90 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 124 283 (accept_3_3 89 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 124 283 (Polychromatic418967fa.accept_16_8_12_11_1_3697 88 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87
  124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 124 283 (accept_3_3 86
  124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 124 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 124 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 283 (accept_3_3 83 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 81
  124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 124 283 (accept_3_3 80
  124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 124 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 283 (accept_3_3 77 124 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 124 283 (Polychromatic418967fa.accept_25_1_24_8_1_17355 76 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 124 283 (accept_3_3 74 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 283 (accept_3_3 71 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 283 (accept_3_3 68 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 283 (accept_3_3 65 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 124 283 (accept_3_3 62 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 124 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 61 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 124 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 283 (accept_3_3 59 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 283 (accept_3_3 56 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 283 (Polychromatic418967fa.accept_15_9_4_13_1_4482 54 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 283 (accept_3_3 53 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 124
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 283 (accept_3_3 50 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 283 (accept_3_3 47 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 283 (accept_3_3 44 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 283 (accept_3_3 41 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 124 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 283 (accept_3_3 38 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 283 (accept_3_3 35 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 283 (accept_3_3 32 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 283 (accept_3_3 29 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 283 (accept_3_3 26 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 283 (accept_3_3 23 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 283 (accept_3_3 20 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 283 (Polychromatic418967fa.accept_19_18_10_17_1_5192 18 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 283 (accept_3_3 17 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 124 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 283 (accept_3_3 14 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 283 (Polychromatic418967fa.accept_20_13_4_3_1_14612 13 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 283 (accept_3_3 11 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 283 (accept_3_3 8 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 283 (accept_3_3 5 124 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 124 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 283 (accept_3_3 2 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 123 283 (allA_succ_of_accept 122 123 283 (accept_3_3 122 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 123 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 121 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21
  120 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 283 (accept_3_3
  119 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 118 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 123 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 117 123 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 283 (accept_3_3 116 123 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 115 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 114 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 123 283 (accept_3_3 113 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 123 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 111 123
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 283 (accept_3_3 110 123
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 283
  (Polychromatic418967fa.accept_9_1_6_4_1_49 109 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 123 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 108 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 283 (accept_3_3 107 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 105 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 123 283 (accept_3_3 104 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 123 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 103 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 283 (accept_3_3 101 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 123
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 123 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 123 283 (accept_3_3 98 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 123 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 96 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 283 (accept_3_3 95 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 93 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 123 283 (accept_3_3 92 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 123 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 283 (accept_3_3 89 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 283
  (Polychromatic418967fa.accept_13_9_6_10_1_666 87 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 123 283 (accept_3_3 86 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 123 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 283 (accept_3_3 83 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 123 283 (accept_3_3 80 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 123 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 283 (accept_3_3 77 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 123 283 (accept_3_3 74 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 123 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 123 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 72 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 283 (accept_3_3 71 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 123 283 (accept_3_3 68 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 123 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 67 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 123 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 283 (accept_3_3 65 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 283
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 123 283 (accept_3_3 62 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 123 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 123 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 283 (accept_3_3 59 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 123 283 (accept_3_3 56 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 123 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 283 (accept_3_3 53 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 51 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 123 283 (accept_3_3 50 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 123 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 283 (accept_3_3 47 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 123 283 (accept_3_3 44 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 123 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 283 (accept_3_3 41 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 283 (accept_3_3 38 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 123 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 283 (accept_3_3 35 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 283 (accept_3_3 32 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 283 (accept_3_3 29 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 283 (accept_3_3 26 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 283 (accept_3_3 23 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 283 (accept_3_3 20 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 283 (accept_3_3 17 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 283 (accept_3_3 14 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 283 (accept_3_3 11 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 283 (accept_3_3 8 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 283 (accept_3_3 5 123 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 283 (accept_3_3 2 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_283_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


