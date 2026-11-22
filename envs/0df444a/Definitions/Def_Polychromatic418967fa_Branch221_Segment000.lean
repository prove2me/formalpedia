-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch221_Segment000
-- name    : Polychromatic418967fa_Branch221_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:34:13.581158+00:00
-- url     : https://prove2.me/theorems/bd9267f5-1311-41c8-8cdb-737bf2174efb
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

def Polychromatic418967fa.branch_221_segment_000 : allB 125 221 :=
  allB_succ' 98 124 221 (Eq.refl Bool.true) (allA_of_3_0 98 124 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  99 123 221 (Eq.refl Bool.true) (allA_succ_of_accept 98 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 221 (accept_3_2 97 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 221 (Polychromatic418967fa.accept_15_6_3_11_1_848
  96 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 221
  (Polychromatic418967fa.accept_25_20_23_21_1_7825 95 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 123 221 (accept_3_2 94 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 123 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 221 (accept_3_2 91 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90
  123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 221 (accept_3_2 88 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 221 (accept_3_2 85 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 221 (accept_3_2 82 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 221 (accept_3_2 79 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 221
  (Polychromatic418967fa.accept_19_1_9_12_1_6207 77 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 221 (accept_3_2 76 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 221 (accept_3_2 73 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 221 (accept_3_2 70 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 221 (accept_3_2 67 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 221 (accept_3_2 64 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 221 (Polychromatic418967fa.accept_18_9_15_5_1_6551 63 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 221 (accept_3_2 61 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 59 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 221 (accept_3_2 58 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 221 (accept_3_2 55 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 221 (accept_3_2 52 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 221 (accept_3_2 49 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 221 (accept_3_2 46 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 221 (accept_3_2 43 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 221
  (Polychromatic418967fa.accept_19_3_9_12_1_6253 41 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 221 (accept_3_2 40 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 221 (accept_3_2 37 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 221 (accept_3_2 34 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 221 (accept_3_2 31 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 221 (accept_3_2 28 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 221 (Polychromatic418967fa.accept_18_9_15_5_1_6551 27 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 221 (accept_3_2 25 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 221 (Polychromatic418967fa.accept_16_8_11_13_1_7265 24 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 221
  (Polychromatic418967fa.accept_15_8_3_11_1_849 23 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 221 (accept_3_2 22 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 221 (accept_3_2 19 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 221 (accept_3_2 16 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 221 (Polychromatic418967fa.accept_26_15_19_13_1_13176 15 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 221 (accept_3_2 13 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 123 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 221 (accept_3_2 10 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 221 (accept_3_2 7 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 221
  (Polychromatic418967fa.accept_19_5_9_12_1_11778 5 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 221 (accept_3_2 4 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 221 (accept_3_2 1 123 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  122 221 (Eq.refl Bool.true) (allA_succ_of_accept 99 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 122 221
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 98 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 122 221 (accept_3_2 97 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 122 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 96 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 122 221 (accept_3_2 94 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 122 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 92 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 122 221 (accept_3_2 91 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 122 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 122 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 89 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 122 221 (accept_3_2 88 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 122 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 122 221 (accept_3_2 85 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 122 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 84 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 122 221 (accept_3_2 82 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 122 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 122 221 (accept_3_2 79 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 122 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 122 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 77 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 122 221 (accept_3_2 76 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 122 221
  (Polychromatic418967fa.accept_22_8_12_1_1_13175 74 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 122 221 (accept_3_2 73 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 122 221 (Polychromatic418967fa.accept_19_15_8_12_1_1286 72 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 122 221 (accept_3_2 70
  122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 122 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 122 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 68 122 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 221 (accept_3_2 67 122 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 122 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 221 (accept_3_2 64 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 221 (accept_3_2 61 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 221 (Polychromatic418967fa.accept_16_12_10_13_1_1042 60 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 221 (accept_3_2 58 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 221 (accept_3_2 55 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 122
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 221
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 221 (accept_3_2 52 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 221 (accept_3_2 49 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 221 (accept_3_2 46 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 221 (accept_3_2 43 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 221 (Polychromatic418967fa.accept_19_4_8_12_1_4757 42 122
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 221 (accept_3_2 40 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 221 (Polychromatic418967fa.accept_22_16_12_1_1_13174 38 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 221 (accept_3_2 37 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 221 (accept_3_2 34 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 221 (accept_3_2 31 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 221 (Polychromatic418967fa.accept_16_14_10_13_1_2768 30
  122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 221 (accept_3_2 28 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 221 (accept_3_2 25 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 24 122
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 221 (accept_3_2 22 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 221 (accept_3_2 19 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 221 (Polychromatic418967fa.accept_23_18_7_14_1_13173 18 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 221
  (Polychromatic418967fa.accept_23_17_7_14_1_13172 17 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 122 221 (accept_3_2 16 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 221 (Polychromatic418967fa.accept_16_14_10_13_1_2768 14
  122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 221 (accept_3_2 13
  122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 221
  (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 221 (accept_3_2 10 122 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 221 (accept_3_2 7 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 221 (accept_3_2 4 122 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 221
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 2 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 221 (accept_3_2 1 122 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 121 221 (Eq.refl Bool.true) (allA_of_3_0 101 121 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 120
  221 (Eq.refl Bool.true) (allA_succ_of_accept 101 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 221 (accept_3_2 100 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 221
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 99 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 221 (accept_3_2 97 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 221
  (Polychromatic418967fa.accept_26_17_16_13_1_13171 95 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 120 221 (accept_3_2 94 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 120 221 (Polychromatic418967fa.accept_19_17_6_12_1_7757 93 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 92
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 120 221 (accept_3_2 91
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 120 221
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 221 (accept_3_2 88 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 221 (Polychromatic418967fa.accept_11_9_10_1_1_581
  86 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 221 (accept_3_2 85
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 120 221
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 84 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 120 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 221 (accept_3_2 82 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 120 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 81 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 221 (accept_3_2 79 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 221 (Polychromatic418967fa.accept_22_11_10_1_1_8437 77 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 221 (accept_3_2 76 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 221 (accept_3_2 73 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 221 (Polychromatic418967fa.accept_19_15_6_12_1_7746 72 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 221 (accept_3_2 70 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 221 (accept_3_2 67 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 221 (accept_3_2 64 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 63 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 221 (accept_3_2 61 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 221 (accept_3_2 58 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 221 (accept_3_2 55 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 221 (accept_3_2 52 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 221
  (Polychromatic418967fa.accept_34_16_18_17_1_13170 50 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 120 221 (accept_3_2 49 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 120 221 (Polychromatic418967fa.accept_19_10_6_12_1_10562 48 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122
  47 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 221 (accept_3_2 46
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 120 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 221 (accept_3_2 43 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 221
  (Polychromatic418967fa.accept_22_19_10_1_1_13169 41 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 120 221 (accept_3_2 40 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 120 221 (Polychromatic418967fa.accept_28_11_8_25_1_13168 39 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121
  38 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 221 (accept_3_2 37
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 221
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 221 (accept_3_2 34 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 221 (Polychromatic418967fa.accept_14_4_8_11_1_794
  32 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 221 (accept_3_2 31
  120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 221
  (Polychromatic418967fa.accept_21_9_15_11_1_7018 30 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 221 (accept_3_2 28 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 221 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 221 (accept_3_2 25 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 221 (Polychromatic418967fa.accept_19_4_6_12_1_13144 23 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 221 (accept_3_2 22 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 221 (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 120
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 221 (accept_3_2 19 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 221 (accept_3_2 16 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 221
  (Polychromatic418967fa.accept_19_14_6_12_1_13167 14 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 221 (accept_3_2 13 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 221 (accept_3_2 10 120 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 221 (Polychromatic418967fa.accept_11_9_10_1_1_581
  9 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 221 (accept_3_2 7 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 221 (accept_3_2 4 120 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 221 (accept_3_2 1 120 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 119 221 (Eq.refl Bool.true) (allA_succ_of_gcd 102 119 221 17 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 119 221 (Polychromatic418967fa.accept_14_3_7_11_1_765
  101 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 221 (accept_3_2
  100 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 221
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 99 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 221 (accept_3_2 97 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 119 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 221 (Polychromatic418967fa.accept_10_5_9_1_1_187
  95 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 221 (accept_3_2 94
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 221
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 119 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 92 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 221 (accept_3_2 91 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 221 (Polychromatic418967fa.accept_9_8_2_5_1_237
  89 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 221 (accept_3_2 88
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 221
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 119 221 17 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 84
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 221
  (Polychromatic418967fa.accept_19_7_5_12_1_7756 83 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 221 (accept_3_2 82 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 221 (Polychromatic418967fa.accept_21_18_14_11_1_7035 81 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 221 (accept_3_2 79 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 221
  (Polychromatic418967fa.accept_19_1_5_12_1_6249 77 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 221 (accept_3_2 76 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 221 (accept_3_2 73 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 221 (accept_3_2 70 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 119 221 17 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 119 221 (accept_3_2 67 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 221 (accept_3_2 64 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 221
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 221 (accept_3_2 61 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 221
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 221 (accept_3_2 58 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 221 (Polychromatic418967fa.accept_22_12_9_1_1_13113 56 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 221 (accept_3_2 55 119 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 221 (accept_3_2 52 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51
  119 221 17 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 119 221 (accept_3_2 49 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 221 (Polychromatic418967fa.accept_19_9_5_12_1_7728 47 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 221 (accept_3_2 46 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 221 (accept_3_2 43 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 221
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 41 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 221 (accept_3_2 40 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 221 (accept_3_2 37 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 221 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 119 221 17 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 119 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 221 (accept_3_2 31 119
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 221
  (Polychromatic418967fa.accept_21_8_14_11_1_11676 29 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 119 221 (accept_3_2 28 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 119 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 221 (accept_3_2 25
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 221
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 221 (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 221 (accept_3_2 22 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 221
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 221 (accept_3_2 19 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 119 221 17 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 119 221 (accept_3_2 16 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 221 (accept_3_2 13 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234
  12 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 221
  (Polychromatic418967fa.accept_19_11_5_12_1_3439 11 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 221 (accept_3_2 10 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 221 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 119 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 221 (accept_3_2 7 119 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 221 (accept_3_2 4 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 221 (accept_3_2 1 119 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 118 221 (Eq.refl Bool.true) (allA_of_3_0 104 118 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 117
  221 (Eq.refl Bool.true) (allA_succ_of_gcd 104 117 221 13 8 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 117 221 (accept_3_2 103 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 117 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 102 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 221
  (Polychromatic418967fa.accept_25_1_17_21_1_13166 101 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 221 (accept_3_2 100 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 117 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 221 (accept_3_2 97 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297
  96 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 221
  (Polychromatic418967fa.accept_23_3_2_14_1_13165 95 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 117 221 (accept_3_2 94 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 117 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 117 221 13 7 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 117 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 89 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 221 (accept_3_2 88 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 221 (accept_3_2 85 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 221 (accept_3_2 82 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 221 (Polychromatic418967fa.accept_16_1_5_13_1_1025 81 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 221 (accept_3_2 79 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  117 221 13 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 117 221 (Polychromatic418967fa.accept_21_14_12_11_1_3956 77 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 221 (accept_3_2 76 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 117 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 221 (accept_3_2 73 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 221 (Polychromatic418967fa.accept_7_2_5_4_1_115
  72 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 221 (accept_3_2 70 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 221 (accept_3_2 67 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 66 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 117 221 13 5 9 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 221 (accept_3_2 64 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 221 (Polychromatic418967fa.accept_12_3_9_5_1_853
  63 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 221 (accept_3_2 61 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 221 (Polychromatic418967fa.accept_21_18_12_11_1_7078 60 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 59 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 221 (accept_3_2 58 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 221 (Polychromatic418967fa.accept_7_1_5_4_1_134
  57 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 221 (accept_3_2 55 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 221 (Polychromatic418967fa.accept_15_8_12_11_1_1570 53 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 117 221 13 4 9 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 117 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 221 (accept_3_2 49 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 221
  (Polychromatic418967fa.accept_19_9_3_12_1_6191 47 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 221 (accept_3_2 46 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 221 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 221 (accept_3_2 43 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 221 (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 221 (accept_3_2 40 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39
  117 221 13 3 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 117 221 (accept_3_2 37 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 117 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 221 (Polychromatic418967fa.accept_21_14_12_11_1_3956 35
  117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 221 (accept_3_2 34
  117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 221
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 221 (accept_3_2 31 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 221 (Polychromatic418967fa.accept_7_1_5_4_1_134
  29 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 221 (accept_3_2 28
  117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 117 221 13 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 117 221 (accept_3_2 25 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 221 (accept_3_2 22 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 221 (Polychromatic418967fa.accept_19_2_3_12_1_10559 21 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 221 (accept_3_2 19 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 221 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 221 (accept_3_2 16 117 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 117 221 13 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 117 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 221 (Polychromatic418967fa.accept_19_11_3_12_1_6138 11 117
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 221 (accept_3_2 10 117
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 221 (accept_3_2 7 117 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 221
  (Polychromatic418967fa.accept_21_5_12_11_1_5429 5 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 221 (accept_3_2 4 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 117 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 221 (accept_3_2 1 117 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 116 221 (Eq.refl Bool.true) (allA_succ_of_accept 105 116 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 116 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 104 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 221 (accept_3_2 103 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 116 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 221 (accept_3_2 100 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 221 (accept_3_2 97 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 95 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 221 (accept_3_2 94 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 221 (accept_3_2 91 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 221 (Polychromatic418967fa.accept_19_14_2_12_1_13164 90 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 89 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 221 (accept_3_2 88 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 86 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 221 (accept_3_2 85 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 221 (accept_3_2 82 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 221 (Polychromatic418967fa.accept_19_4_2_12_1_10527 80 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 221 (accept_3_2 79 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 221
  (Polychromatic418967fa.accept_10_7_6_1_1_486 77 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 221 (accept_3_2 76 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 221 (accept_3_2 73 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 221
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 221 (accept_3_2 70 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 221 (Polychromatic418967fa.accept_18_14_8_5_1_860 68 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 221 (accept_3_2 67 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 221 (accept_3_2 64 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 221 (accept_3_2 61 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 221
  (Polychromatic418967fa.accept_23_13_1_14_1_11554 59 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 116 221 (accept_3_2 58 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 221 (accept_3_2 55 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 221
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 116 221 (Polychromatic418967fa.accept_18_17_8_5_1_2769 53 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 221 (accept_3_2 52 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 221 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 221 (accept_3_2 49
  116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 221 (accept_3_2 46 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 221
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 44 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 116 221 (accept_3_2 43 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 116 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 221 (accept_3_2 40 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39
  116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 221 (accept_3_2 37 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 221 (accept_3_2 34 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 221 (accept_3_2 31 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 221 (accept_3_2 28 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 221 (accept_3_2 25 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 221 (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 221 (accept_3_2 22 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 221 (accept_3_2 19 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 221 (accept_3_2 16 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 221 (accept_3_2 13 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 221 (accept_3_2 10 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 221 (accept_3_2 7 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 221 (accept_3_2 4 116 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 221 (accept_3_2 1 116 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 115 221 (Eq.refl Bool.true) (allA_of_3_0 107 115 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 114 221 (Eq.refl Bool.true) (allA_succ_of_accept 107 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 107 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 114 221 (accept_3_2 106 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 114 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 105 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 114 221 (accept_3_2 103 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 114
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 114 221 (accept_3_2 100 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 221 (accept_3_2 97 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 114 221 (accept_3_2 94 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 114 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 221 (accept_3_2 91 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 89 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 221 (accept_3_2 88 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 114 221 (Polychromatic418967fa.accept_20_6_14_1_1_8896 86 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 221 (accept_3_2 85 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 114 221 (accept_3_2 82 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 114 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 114 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 221 (accept_3_2 79 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 221 (Polychromatic418967fa.accept_21_15_9_11_1_5417 78 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 221
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 221 (accept_3_2 76 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 114 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 221 (accept_3_2 73 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 221 (Polychromatic418967fa.accept_27_18_6_5_1_13163 72 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 221 (accept_3_2 70 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 221 (accept_3_2 67 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 221 (accept_3_2 64 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 221 (accept_3_2 61 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 221 (Polychromatic418967fa.accept_21_18_9_11_1_7082 60 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 221 (accept_3_2 58 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 114 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 221 (accept_3_2 55 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 221 (accept_3_2 52 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 221 (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 221 (accept_3_2 49 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 221 (accept_3_2 46 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 221 (accept_3_2 43 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 221 (Polychromatic418967fa.accept_25_17_14_21_1_13162 42 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 221 (accept_3_2 40 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 221 (accept_3_2 37 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 221 (accept_3_2 34 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 221 (accept_3_2 31 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 221 (accept_3_2 28 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 221 (accept_3_2 25 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 221 (Polychromatic418967fa.accept_27_24_6_5_1_13161 24 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 221 (accept_3_2 22 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 221 (accept_3_2 19 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 221 (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 221 (accept_3_2 16 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 221 (Polychromatic418967fa.accept_26_14_10_13_1_13160 14 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 221 (accept_3_2 13 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 221 (accept_3_2 10 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 221 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 221 (accept_3_2 7 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 221 (accept_3_2 4 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 221 (accept_3_2 1 114 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 113 221 (Eq.refl Bool.true) (allA_succ_of_accept 108 113 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 108 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 221 (Polychromatic418967fa.accept_24_11_17_5_1_7968 107 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 221 (accept_3_2 106 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 221 (Polychromatic418967fa.accept_16_9_1_13_1_1850 105 113 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 221
  (Polychromatic418967fa.accept_19_9_18_12_1_2286 104 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 221 (accept_3_2 103 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 102 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 221 (accept_3_2 100 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 221
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 99 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 98 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 221 (accept_3_2 97 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 95 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 113 221 (accept_3_2 94 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 113 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 93 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 113 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 92 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 221 (accept_3_2 91 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 89 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 221 (accept_3_2 88 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 221 (Polychromatic418967fa.accept_22_20_3_1_1_13159 86 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 221 (accept_3_2 85 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 113 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 221
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 83 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 221 (accept_3_2 82 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 221 (Polychromatic418967fa.accept_21_18_8_11_1_10083 81 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 80 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 221 (accept_3_2 79 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 221
  (Polychromatic418967fa.accept_19_1_18_12_1_7755 77 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 113 221 (accept_3_2 76 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 74 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 221 (accept_3_2 73 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 221
  (Polychromatic418967fa.accept_10_2_3_1_1_481 72 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 113 221 (Polychromatic418967fa.accept_22_5_3_1_1_13158 71 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 221 (accept_3_2 70 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 113 221 (Polychromatic418967fa.accept_16_5_1_13_1_1053 69 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 221 (accept_3_2 67 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 221 (accept_3_2 64 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 221
  (Polychromatic418967fa.accept_10_2_3_1_1_481 62 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 221 (accept_3_2 61 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 221 (accept_3_2 58 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 221
  (Polychromatic418967fa.accept_21_14_8_11_1_10082 56 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 113 221 (accept_3_2 55 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 221 (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 221 (accept_3_2 52 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 221
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 51 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 113 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 50 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 221 (accept_3_2 49 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 113 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 221 (accept_3_2 46 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 221 (accept_3_2 43 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 221
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 41 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 221 (accept_3_2 40 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 221 (Polychromatic418967fa.accept_19_1_18_12_1_7755 39 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 221 (accept_3_2 37 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 221
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 221 (accept_3_2 34 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 221 (accept_3_2 31 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 221 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 113
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 221
  (Polychromatic418967fa.accept_23_6_21_14_1_13157 29 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 113 221 (accept_3_2 28 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 113 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122
  26 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 221 (accept_3_2 25
  113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 221 (Polychromatic418967fa.accept_20_3_13_1_1_8886 23 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 221 (accept_3_2 22 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 221 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 221
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 221 (accept_3_2 19 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 221 (accept_3_2 16 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 221 (Polychromatic418967fa.accept_19_15_18_12_1_6180 15 113 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 221
  (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 221 (accept_3_2 13 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 221 (Polychromatic418967fa.accept_19_11_18_12_1_4802 11
  113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 221 (accept_3_2 10
  113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 221
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 113 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 221 (accept_3_2 7 113 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 113 221 (Polychromatic418967fa.accept_19_6_18_12_1_6125 6 113 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 221 (accept_3_2 4 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 221 (accept_3_2 1 113 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 112 221 (Eq.refl Bool.true) (allA_of_3_0 110 112 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 111 221 (allA_succ_of_accept 110 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 221 (accept_3_2 109 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 111
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 107 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 221 (accept_3_2 106 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 221 (accept_3_2 103 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 101 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 221 (accept_3_2 100 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 99 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 221 (accept_3_2 97 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 221
  (Polychromatic418967fa.accept_15_5_6_11_1_854 95 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 221 (accept_3_2 94 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 221 (accept_3_2 91 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 221 (accept_3_2 88 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 221 (accept_3_2 85 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 84 111 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 221 (accept_3_2 82 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 221 (accept_3_2 79 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 77 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 221 (accept_3_2 76 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 221 (accept_3_2 73 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 221 (accept_3_2 70 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 221 (accept_3_2 67 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 221 (accept_3_2 64 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 221 (accept_3_2 61 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 221 (accept_3_2 58 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 221 (accept_3_2 55 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 221 (accept_3_2 52 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 221 (accept_3_2 49 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 221 (accept_3_2 46 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 221 (accept_3_2 43 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 221
  (Polychromatic418967fa.accept_21_20_6_11_1_2623 41 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 111 221 (accept_3_2 40 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 111 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 111 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 221 (accept_3_2 37 111 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 221
  (Polychromatic418967fa.accept_20_16_11_1_1_10407 36 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 221 (accept_3_2 34 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 221 (accept_3_2 31 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 221 (accept_3_2 28 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 221 (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 111 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 221 (accept_3_2 25 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 221 (accept_3_2 22 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 221 (accept_3_2 19 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 221 (accept_3_2 16 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 221 (accept_3_2 13 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 221 (accept_3_2 10 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 221 (accept_3_2 7 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 221 (accept_3_2 4 111 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 221 (accept_3_2 1 111 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 221 (allA_succ_of_accept 109 110 221 (accept_3_2 109 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 221 (Polychromatic418967fa.accept_23_16_18_14_1_13156 108 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50
  107 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 221 (accept_3_2
  106 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 110 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 221 (accept_3_2 103 110 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 221
  (Polychromatic418967fa.accept_19_6_15_12_1_6263 101 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 110 221 (accept_3_2 100 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 110 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 221 (accept_3_2 97 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 221 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 221 (accept_3_2 94 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 221 (accept_3_2 91 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 221 (accept_3_2 88 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 221 (accept_3_2 85 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 221 (accept_3_2 82 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 221 (accept_3_2 79 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 221 (accept_3_2 76 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 221 (Polychromatic418967fa.accept_16_10_14_13_1_1870 74 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 221 (accept_3_2 73 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 221 (accept_3_2 70 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 68 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 221 (accept_3_2 67 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 221 (accept_3_2 64 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 221 (accept_3_2 61 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 221 (accept_3_2 58 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 221 (accept_3_2 55 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 221 (Polychromatic418967fa.accept_15_9_5_11_1_5416 54 110
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 221 (accept_3_2 52 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 221 (accept_3_2 49 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 221 (accept_3_2 46 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 221 (accept_3_2 43 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 221 (accept_3_2 40 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 221 (accept_3_2 37 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 221 (accept_3_2 34 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 221 (accept_3_2 31 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 221 (accept_3_2 28 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 221 (accept_3_2 25 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 221 (accept_3_2 22 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 221 (accept_3_2 19 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 221 (Polychromatic418967fa.accept_19_18_15_12_1_11773 18 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 221 (accept_3_2 16 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 221 (Polychromatic418967fa.accept_20_14_10_1_1_13086 14 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 221 (accept_3_2 13 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 221 (accept_3_2 10 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 221 (accept_3_2 7 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 221
  (Polychromatic418967fa.accept_19_5_15_12_1_6273 5 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 221 (accept_3_2 4 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 221 (accept_3_2 1 110 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 221 (allA_of_3_0 109 109 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 221
  (allA_succ_of_accept 107 108 221 (Polychromatic418967fa.accept_20_7_8_1_1_5856 107 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 221 (accept_3_2 106 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 105 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 104 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 221 (accept_3_2 103 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 221 (Polychromatic418967fa.accept_21_18_3_11_1_7049 102 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 221 (Polychromatic418967fa.accept_19_6_13_12_1_6220 101 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 221 (accept_3_2 100 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128
  99 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 98 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 221 (accept_3_2 97 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 96 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 221 (Polychromatic418967fa.accept_16_15_12_13_1_1045 95 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 221 (accept_3_2 94 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 93 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 92 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 221 (accept_3_2 91 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 89 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 221 (accept_3_2 88 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 221
  (Polychromatic418967fa.accept_25_11_8_21_1_13124 86 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 108 221 (accept_3_2 85 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 108 221 (Polychromatic418967fa.accept_16_4_12_13_1_990 84 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 221 (accept_3_2 82 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 81
  108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 221
  (Polychromatic418967fa.accept_22_14_20_1_1_6722 80 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 108 221 (accept_3_2 79 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 77 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 221 (accept_3_2 76 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 221
  (Polychromatic418967fa.accept_19_18_13_12_1_4775 75 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 108 221 (Polychromatic418967fa.accept_15_14_3_11_1_850 74 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 221 (accept_3_2 73 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 108 221 (accept_3_2 70 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 108 221 (Polychromatic418967fa.accept_15_8_3_11_1_849 68 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 221 (accept_3_2 67 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 221 (accept_3_2 64 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 108 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 221 (accept_3_2 61 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 221 (Polychromatic418967fa.accept_19_3_13_12_1_10525 60 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 221
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 221 (accept_3_2 58 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 108 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 221 (accept_3_2 55 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 221
  (Polychromatic418967fa.accept_10_3_8_1_1_182 53 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 221 (accept_3_2 52 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 108 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 221 (accept_3_2 49 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 221
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 47 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 108 221 (accept_3_2 46 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 108 221 (Polychromatic418967fa.accept_25_20_8_21_1_13155 45 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 44 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 221 (accept_3_2 43 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 221 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 221 (accept_3_2 40 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 221
  (Polychromatic418967fa.accept_15_8_3_11_1_849 38 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 221 (accept_3_2 37 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 108 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 35 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 221 (accept_3_2 34 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 221 (accept_3_2 31 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 221 (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 221 (accept_3_2 28 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 221
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 26 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 108 221 (accept_3_2 25 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 108 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 221 (Polychromatic418967fa.accept_10_3_8_1_1_182
  23 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 221 (accept_3_2 22
  108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 221 (accept_3_2 19 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 221 (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 221 (accept_3_2 16 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 221 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 221 (accept_3_2 13 108 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 221 (Polychromatic418967fa.accept_21_12_3_11_1_10078 12
  108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 221
  (Polychromatic418967fa.accept_19_11_13_12_1_6259 11 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 108 221 (accept_3_2 10 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 108 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 221 (accept_3_2 7 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 221
  (Polychromatic418967fa.accept_19_5_13_12_1_13154 5 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 108 221 (accept_3_2 4 108 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 108 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 221 (Polychromatic418967fa.accept_23_2_16_14_1_11540 2 108
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 221 (accept_3_2 1 108 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 221 (allA_succ_of_accept 106 107 221 (accept_3_2 106 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 105 107 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 107
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 221 (accept_3_2 103 107
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 107 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 221 (accept_3_2 100 107 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 99 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 221 (accept_3_2 97 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 95 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 221 (accept_3_2 94 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 93 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 221 (accept_3_2 91 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 221 (accept_3_2 88 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 221 (accept_3_2 85 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 221 (accept_3_2 82 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 80 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 221 (accept_3_2 79 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 221 (Polychromatic418967fa.accept_21_14_2_11_1_8625 77 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 221 (accept_3_2 76 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 221 (accept_3_2 73 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 221 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 221 (Polychromatic418967fa.accept_20_11_7_1_1_8874 71 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 221 (accept_3_2 70 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 221 (accept_3_2 67 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 221 (accept_3_2 64 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 221 (Polychromatic418967fa.accept_25_13_7_21_1_11411 63 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 221 (accept_3_2 61 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 221 (accept_3_2 58 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 221 (accept_3_2 55 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 221 (Polychromatic418967fa.accept_25_3_7_21_1_13153 53 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 221 (accept_3_2 52 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 221 (accept_3_2 49 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 221 (accept_3_2 46 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 221 (Polychromatic418967fa.accept_23_22_15_14_1_13152 45 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 221
  (Polychromatic418967fa.accept_10_4_7_1_1_471 44 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 221 (accept_3_2 43 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 221 (accept_3_2 40 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 221 (accept_3_2 37 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 221 (accept_3_2 34 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 221
  (Polychromatic418967fa.accept_22_10_19_1_1_13151 32 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 107 221 (accept_3_2 31 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 221 (accept_3_2 28 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 221 (Polychromatic418967fa.accept_7_6_2_4_1_291
  27 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 221 (accept_3_2 25 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 221 (Polychromatic418967fa.accept_24_23_11_5_1_13150 23 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 221 (accept_3_2 22 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 221 (accept_3_2 19 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 221 (Polychromatic418967fa.accept_21_17_2_11_1_8656 17 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 221 (accept_3_2 16 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 107 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 221 (accept_3_2 13 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 221 (accept_3_2 10 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 221
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 8 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 221 (accept_3_2 7 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 221 (accept_3_2 4 107 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 107 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 221 (accept_3_2 1 107 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 221 (allA_of_3_0 106 106 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 221
  (allA_succ_of_accept 104 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 221 (accept_3_2 103 105 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 221 (accept_3_2 100 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 221 (accept_3_2 97 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 96 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 221
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 95 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 221 (accept_3_2 94 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 221 (accept_3_2 91 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 221 (Polychromatic418967fa.accept_19_14_10_12_1_4809 90 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 221 (accept_3_2 88 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 221 (accept_3_2 85 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 221 (accept_3_2 82 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 221 (Polychromatic418967fa.accept_16_1_9_13_1_1822 81 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 221 (accept_3_2 79 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 78 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 221
  (Polychromatic418967fa.accept_25_2_5_21_1_13149 77 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 105 221 (accept_3_2 76 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 105 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 221 (accept_3_2 73 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 221
  (Polychromatic418967fa.accept_22_6_17_1_1_1004 72 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 105 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 221 (accept_3_2 70 105 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 221 (accept_3_2 67 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 105 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 221 (accept_3_2 64 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 221 (accept_3_2 61 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 105 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 221 (accept_3_2 58 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 221 (accept_3_2 55 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 221 (accept_3_2 52 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 221 (accept_3_2 49 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 221 (accept_3_2 46 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 221 (accept_3_2 43 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 221 (Polychromatic418967fa.accept_19_3_10_12_1_6217 41 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 221 (accept_3_2 40 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 221 (accept_3_2 37 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 221 (accept_3_2 34 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 221 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 221 (accept_3_2 31 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 221 (accept_3_2 28 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 221 (accept_3_2 25 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 221 (Polychromatic418967fa.accept_16_7_9_13_1_4948 23 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 221 (accept_3_2 22 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 221 (accept_3_2 19 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 221 (accept_3_2 16 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 221 (accept_3_2 13 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 221 (accept_3_2 10 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 221 (accept_3_2 7 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 221 (accept_3_2 4 105 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 221 (accept_3_2 1 105 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 221 (allA_succ_of_accept 103 104 221 (accept_3_2 103 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 102 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 221 (Polychromatic418967fa.accept_7_3_6_4_1_30
  101 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 221 (accept_3_2
  100 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 221 (accept_3_2 97 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 221 (Polychromatic418967fa.accept_10_5_4_1_1_842
  95 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 221 (accept_3_2 94
  104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 221 (Polychromatic418967fa.accept_16_12_8_13_1_6073 92 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 104 221 13 7 8 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 104 221
  (Polychromatic418967fa.accept_19_14_9_12_1_9113 90 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 104 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 104 221 (accept_3_2 88 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 104 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 104 221 (accept_3_2 85 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 104 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 84 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 104 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 83 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 104 221 (accept_3_2 82 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 104 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 80 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 104 221 (accept_3_2 79 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  104 221 13 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 104 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 104 221 (accept_3_2 76 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 221 (accept_3_2 73 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 104 221 (Polychromatic418967fa.accept_19_14_9_12_1_9113 71 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 221 (accept_3_2 70 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 221 (accept_3_2 67 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 104 221 13 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 104 221 (accept_3_2 64 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 221 (accept_3_2 61 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 221
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 60 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 221 (accept_3_2 58 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 221
  (Polychromatic418967fa.accept_19_18_9_12_1_6153 56 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 104 221 (accept_3_2 55 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 104 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 221 (Polychromatic418967fa.accept_16_5_8_13_1_2764 53 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 221 13 4 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 104 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 221 (accept_3_2 49 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 104 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 48 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 221 (accept_3_2 46 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 221 (accept_3_2 43 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 104 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 221
  (Polychromatic418967fa.accept_19_3_9_12_1_6253 41 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 221 (accept_3_2 40 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39
  104 221 13 3 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 104 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 104 221 (accept_3_2 37 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 104 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 221 (accept_3_2 34 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 104 221 (Polychromatic418967fa.accept_25_7_4_21_1_5893 32 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 221 (accept_3_2 31 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 104 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 221
  (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 104 221 (accept_3_2 28 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 221 13 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 221 (accept_3_2 25 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 221 (accept_3_2 22 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 221 (accept_3_2 19 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 104
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 221 (accept_3_2 16 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 104 221 13 1 8 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 104 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 104 221 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 221 (accept_3_2 10 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 221
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 8 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 221 (accept_3_2 7 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 221 (accept_3_2 4 104 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 221 (accept_3_2 1 104 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 221 (allA_of_3_0 103 103 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 221 (allA_succ_of_accept 101
  102 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 221 (accept_3_2 100 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 221 (accept_3_2 97 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240
  96 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 221 (accept_3_2 94 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 93 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 221 (accept_3_2 91 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 221 (accept_3_2 88 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 86 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 102 221 17 5 6 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 102 221
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 84 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 221 (accept_3_2 82 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 81 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 221 (accept_3_2 79 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 221 (Polychromatic418967fa.accept_14_7_4_11_1_3038 77 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 221 (accept_3_2 76 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 221 (accept_3_2 73 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 221 (Polychromatic418967fa.accept_19_15_7_12_1_11763 72 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 221 (accept_3_2 70 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 221 17 4 6 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 221 (accept_3_2 67
  102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 221 (accept_3_2 64 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 221 (Polychromatic418967fa.accept_9_8_3_5_1_241
  62 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 221 (accept_3_2 61
  102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 221
  (Polychromatic418967fa.accept_9_6_3_5_1_240 60 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 221 (accept_3_2 58 102 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 221 (accept_3_2 55 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 221 (Polychromatic418967fa.accept_19_16_7_12_1_6252 54 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 221 (accept_3_2 52 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 221 17 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 102
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 221 (accept_3_2 49 102
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 221
  (Polychromatic418967fa.accept_21_6_18_11_1_3960 48 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 221 (accept_3_2 46 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 221 (accept_3_2 43 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 221 (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 221 (accept_3_2 40 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 221 (accept_3_2 37 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 221 17 2 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 221
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 102 221 (Polychromatic418967fa.accept_22_10_14_1_1_13148 32 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 221 (accept_3_2 31 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 221 (Polychromatic418967fa.accept_19_11_7_12_1_4770 30 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 221 (accept_3_2 28 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 221 (accept_3_2 25 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 221 (accept_3_2 22 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 221 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 221 (accept_3_2 19 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 221 (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 102 221 17 1 6 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 102 221 (accept_3_2 16
  102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 221 (accept_3_2 13 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 221 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 102 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 221 (accept_3_2 10 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 221 (accept_3_2 7 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 102 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 221
  (Polychromatic418967fa.accept_19_5_7_12_1_2252 5 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 221 (accept_3_2 4 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 221 (accept_3_2 1 102 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 221 (allA_succ_of_accept 100 101 221 (accept_3_2 100 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 101 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 221 (accept_3_2 97 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 221
  (Polychromatic418967fa.accept_23_3_9_14_1_13147 95 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 101 221 (accept_3_2 94 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 101 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 221 (accept_3_2 91 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294
  90 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 221 (accept_3_2 88 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 86 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 221 (accept_3_2 85 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 221 (accept_3_2 82 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 221 (Polychromatic418967fa.accept_16_1_5_13_1_1025 81 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 221 (accept_3_2 79 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 221
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 221 (accept_3_2 76 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 221 (Polychromatic418967fa.accept_16_10_5_13_1_8591 74 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 221 (accept_3_2 73 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 221 (Polychromatic418967fa.accept_16_8_5_13_1_1021 72 101
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 221 (accept_3_2 70 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 68 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 221 (accept_3_2 67 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 221
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 221 (accept_3_2 64 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 221 (accept_3_2 61 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 221
  (Polychromatic418967fa.accept_19_2_6_12_1_6270 59 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 221 (accept_3_2 58 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 221 (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 221 (accept_3_2 55 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 101
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 221 (accept_3_2 52 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 221 (accept_3_2 49 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 221
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 221 (accept_3_2 46 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 221 (Polychromatic418967fa.accept_23_22_9_14_1_13146 45 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 221 (accept_3_2 43 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 221 (accept_3_2 40 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 221 (Polychromatic418967fa.accept_23_15_9_14_1_13145 38 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 221 (accept_3_2 37 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 221 (accept_3_2 34 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 221 (accept_3_2 31 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 221 (accept_3_2 28 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 221 (accept_3_2 25 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 221
  (Polychromatic418967fa.accept_19_4_6_12_1_13144 23 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 101 221 (accept_3_2 22 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 221 (accept_3_2 19 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 221
  (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 101 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 221 (accept_3_2 16 101 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 101 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 221 (Polychromatic418967fa.accept_11_3_2_1_1_994
  14 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 221 (accept_3_2 13
  101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 221
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 101 221 (Polychromatic418967fa.accept_25_11_1_21_1_13143 11 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 221 (accept_3_2 10 101 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 221 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 221 (accept_3_2 7 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 221 (Polychromatic418967fa.accept_21_5_17_11_1_7021 5 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 221 (accept_3_2 4 101 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 221
  (Polychromatic418967fa.accept_16_2_5_13_1_3842 2 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 221 (accept_3_2 1 101 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 221 (allA_of_3_0 100 100 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 221 (allA_succ_of_accept 98 99
  221 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 221 (accept_3_2 97 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 221 (accept_3_2 94 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 221 (accept_3_2 91 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 221 (accept_3_2 88 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 221 (accept_3_2 85 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 84 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 221 (Polychromatic418967fa.accept_19_7_4_12_1_4769 83 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 221 (accept_3_2 82 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 221 (accept_3_2 79 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 77 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 221 (accept_3_2 76 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 221 (accept_3_2 73 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 221 (Polychromatic418967fa.accept_26_19_21_13_1_13142 71 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 221 (accept_3_2 70 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 221 (accept_3_2 67 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 221 (accept_3_2 64 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 221 (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 221 (accept_3_2 61 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 60 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 221 (accept_3_2 58 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 221 (accept_3_2 55 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 221 (Polychromatic418967fa.accept_25_3_24_21_1_9710 53 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 221 (accept_3_2 52 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 221 (accept_3_2 49 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 221 (accept_3_2 46 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 221 (accept_3_2 43 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 221 (Polychromatic418967fa.accept_22_19_11_1_1_13116 41 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 221 (accept_3_2 40 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 221 (Polychromatic418967fa.accept_19_1_4_12_1_6275 39 99
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 221 (accept_3_2 37 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 221 (accept_3_2 34 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 221 (accept_3_2 31 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 221 (Polychromatic418967fa.accept_22_7_11_1_1_6711 29 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 221 (accept_3_2 28 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 221 (Polychromatic418967fa.accept_19_8_4_12_1_4768 27 99
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 221 (accept_3_2 25 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 221 (Polychromatic418967fa.accept_27_23_18_5_1_13141 23 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 221 (accept_3_2 22 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 221 (accept_3_2 19 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 221 (accept_3_2 16 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 221 (accept_3_2 13 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 221 (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 221 (accept_3_2 10 99 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 221 (accept_3_2 7 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 221 (accept_3_2 4 99 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 221 (accept_3_2 1 99 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  221 (allA_succ_of_accept 97 98 221 (accept_3_2 97 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 221 (accept_3_2 94 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 221 (accept_3_2 91 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 89 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 221 (accept_3_2 88 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 221
  (Polychromatic418967fa.accept_11_9_10_1_1_581 86 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 221 (accept_3_2 85 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 221 (accept_3_2 82 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 221 (accept_3_2 79 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 221 (Polychromatic418967fa.accept_20_17_18_1_1_8880 77 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 221 (accept_3_2 76 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 221 (accept_3_2 73 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 72 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 221 (accept_3_2 70 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 221
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 221 (accept_3_2 67 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 221 (accept_3_2 64 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 221
  (Polychromatic418967fa.accept_21_20_14_11_1_13099 62 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 98 221 (accept_3_2 61 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 98 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 98 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 221 (accept_3_2 58 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57
  98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 221 (accept_3_2 55 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 221 (Polychromatic418967fa.accept_21_12_14_11_1_3921 54 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 221 (accept_3_2 52 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 50 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 221 (accept_3_2 49 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 221 (accept_3_2 46 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 221 (accept_3_2 43 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 221 (Polychromatic418967fa.accept_21_20_14_11_1_13099 41 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 221 (accept_3_2 40 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 221 (accept_3_2 37 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 221 (Polychromatic418967fa.accept_19_17_3_12_1_13140 36 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 221 (accept_3_2 34 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 221 (accept_3_2 31 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 221 (accept_3_2 28 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 221
  (Polychromatic418967fa.accept_19_7_3_12_1_4787 26 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 221 (accept_3_2 25 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 221 (accept_3_2 22 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 221 (accept_3_2 19 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 221 (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 221 (accept_3_2 16 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 221
  (Polychromatic418967fa.accept_18_14_8_5_1_860 14 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 221 (accept_3_2 13 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 221 (accept_3_2 10 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 221 (accept_3_2 7 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 98 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 221 (accept_3_2 4 98 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 221 (accept_3_2 1 98 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  221 (allA_of_3_0 97 97 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 221 (allA_succ_of_accept 95 96 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 95 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 221 (accept_3_2 94 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 221 (accept_3_2 91 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 221 (accept_3_2 88 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 87 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 221 (accept_3_2 85 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 221 (accept_3_2 82 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 221 (accept_3_2 79 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 221
  (Polychromatic418967fa.accept_10_7_6_1_1_486 77 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 221 (accept_3_2 76 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 221 (accept_3_2 73 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 221 (accept_3_2 70 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 68 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 221 (accept_3_2 67 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 96 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 221 (accept_3_2 64 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 221 (accept_3_2 61 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 221 (Polychromatic418967fa.accept_21_18_12_11_1_7078 60 96 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 221
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 221 (accept_3_2 58 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 221 (accept_3_2 55 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 221 (accept_3_2 52 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 221 (accept_3_2 49 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 221 (accept_3_2 46 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 221 (accept_3_2 43 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 221 (accept_3_2 40 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 221 (accept_3_2 37 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 221 (accept_3_2 34 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 221 (accept_3_2 31 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 221 (accept_3_2 28 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 221 (accept_3_2 25 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 221 (accept_3_2 22 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 221 (accept_3_2 19 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 221 (accept_3_2 16 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 221 (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 221 (accept_3_2 13 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 221 (accept_3_2 10 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 221 (accept_3_2 7 96 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 221 (accept_3_2 4 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 96 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 221 (accept_3_2 1 96 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 221
  (allA_succ_of_accept 94 95 221 (accept_3_2 94 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 221 (Polychromatic418967fa.accept_24_21_23_5_1_13092 93 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 92 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 221 (accept_3_2 91 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 89 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 221 (accept_3_2 88 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 221 (Polychromatic418967fa.accept_20_7_15_1_1_13089 87 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 221 (accept_3_2 85 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 221
  (Polychromatic418967fa.accept_11_6_7_1_1_564 83 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 221 (accept_3_2 82 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 221 (Polychromatic418967fa.accept_23_11_3_14_1_11556 80 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 221 (accept_3_2 79 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 221 (accept_3_2 76 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 221 (Polychromatic418967fa.accept_26_23_17_13_1_13139 75 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 221 (accept_3_2 73 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 221
  (Polychromatic418967fa.accept_23_2_3_14_1_11509 71 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 221 (accept_3_2 70 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 68 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 221 (accept_3_2 67 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 221
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 221 (accept_3_2 64 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 221 (Polychromatic418967fa.accept_23_17_3_14_1_1773 63 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 221 (accept_3_2 61 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 221 (Polychromatic418967fa.accept_16_12_15_13_1_3872 60 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 221 (accept_3_2 58 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 221 (Polychromatic418967fa.accept_23_11_3_14_1_11556 57 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 221 (accept_3_2 55 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 221 (accept_3_2 52 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 51 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 221 (accept_3_2 49 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 221 (Polychromatic418967fa.accept_22_4_7_1_1_13138 48 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 221 (accept_3_2 46 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 221 (Polychromatic418967fa.accept_20_5_15_1_1_7278 45 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 221 (accept_3_2 43 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 221
  (Polychromatic418967fa.accept_24_17_23_5_1_9756 41 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 221 (accept_3_2 40 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 221 (accept_3_2 37 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 221
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 35 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 221 (accept_3_2 34 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 221 (Polychromatic418967fa.accept_22_11_7_1_1_13135 33 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 221 (accept_3_2 31 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 221 (accept_3_2 28 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 221 (Polychromatic418967fa.accept_20_7_15_1_1_13089 27 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 221 (accept_3_2 25 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 221 (accept_3_2 22 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 221 (Polychromatic418967fa.accept_27_20_14_5_1_13137 20 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 221 (accept_3_2 19 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 221
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 221 (accept_3_2 16 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 221 (Polychromatic418967fa.accept_23_15_3_14_1_13136 15 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 221 (accept_3_2 13 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 221 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 95 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 221
  (Polychromatic418967fa.accept_22_11_7_1_1_13135 11 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 221 (accept_3_2 10 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 221 (accept_3_2 7 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 221
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 5 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 221 (accept_3_2 4 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  221 (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 95 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 221 (accept_3_2 1 95 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 221
  (allA_of_3_0 94 94 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 221 (allA_succ_of_accept 92 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 221 (accept_3_2 91 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 221 (accept_3_2 88 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 221 (accept_3_2 85 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 221 (Polychromatic418967fa.accept_22_18_5_1_1_6729 84 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 221 (accept_3_2 82 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 221 (accept_3_2 79 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 221 (Polychromatic418967fa.accept_25_2_18_21_1_13134 77 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 221 (accept_3_2 76 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 221 (accept_3_2 73 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 221 (accept_3_2 70 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 221 (accept_3_2 67 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 221 (accept_3_2 64 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 221 (accept_3_2 61 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 221 (Polychromatic418967fa.accept_15_14_3_11_1_850 59 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 221 (accept_3_2 58 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 221 (Polychromatic418967fa.accept_21_15_9_11_1_5417 57 93
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 221 (accept_3_2 55 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 221 (accept_3_2 52 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 221 (accept_3_2 49 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 221 (accept_3_2 46 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 221 (Polychromatic418967fa.accept_26_19_15_13_1_13133 45 93 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 221 (accept_3_2 43 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 221 (accept_3_2 40 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 221 (accept_3_2 37 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 221 (accept_3_2 34 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 221 (accept_3_2 31 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 221 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 221 (accept_3_2 28 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 221 (accept_3_2 25 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 221 (Polychromatic418967fa.accept_15_8_3_11_1_849 23 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 221 (accept_3_2 22 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 221 (accept_3_2 19 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 221 (accept_3_2 16 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 221 (accept_3_2 13 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 221 (accept_3_2 10 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 221 (Polychromatic418967fa.accept_22_9_5_1_1_2204 9 93 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 221 (accept_3_2 7 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 221 (accept_3_2 4 93 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 221 (accept_3_2 1 93 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 221
  (allA_succ_of_accept 91 92 221 (accept_3_2 91 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 221 (Polychromatic418967fa.accept_16_10_12_13_1_4950 90 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 221 (accept_3_2 88 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 221 (accept_3_2 85 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 83 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 221 (accept_3_2 82 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 221 (accept_3_2 79 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 221 (Polychromatic418967fa.accept_21_14_8_11_1_10082 77 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 221 (accept_3_2 76 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 221
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 74 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 221 (accept_3_2 73 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 221 (accept_3_2 70 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 221 (accept_3_2 67 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 221 (accept_3_2 64 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 221 (accept_3_2 61 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 221 (accept_3_2 58 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 221 (accept_3_2 55 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 221 (accept_3_2 52 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 221 (accept_3_2 49 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 221 (accept_3_2 46 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 221 (accept_3_2 43 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 221 (accept_3_2 40 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 221 (accept_3_2 37 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 221 (accept_3_2 34 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 221
  (Polychromatic418967fa.accept_14_4_8_11_1_794 32 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 221 (accept_3_2 31 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 221 (accept_3_2 28 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 221 (accept_3_2 25 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 221 (accept_3_2 22 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 221 (accept_3_2 19 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 221 (accept_3_2 16 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 221 (accept_3_2 13 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 221 (Polychromatic418967fa.accept_20_11_12_1_1_13132 11 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 221 (accept_3_2 10 92 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 221 (accept_3_2 7 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 221 (accept_3_2 4 92 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 221 (accept_3_2 1 92 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 221
  (allA_of_3_0 91 91 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 221 (allA_succ_of_accept 89 90 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 221 (accept_3_2 88 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 221 (accept_3_2 85 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 221 (Polychromatic418967fa.accept_20_4_10_1_1_13131 84 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 221 (accept_3_2 82 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 221 (Polychromatic418967fa.accept_21_18_6_11_1_7031 81 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 221 (accept_3_2 79 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 221 (Polychromatic418967fa.accept_16_14_10_13_1_2768 78 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 221
  (Polychromatic418967fa.accept_20_17_10_1_1_11739 77 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 90 221 (accept_3_2 76 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 221 (Polychromatic418967fa.accept_19_17_14_12_1_2263 74 90
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 221 (accept_3_2 73 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 221 (accept_3_2 70 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 221 (accept_3_2 67 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 221 (accept_3_2 64 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 221 (Polychromatic418967fa.accept_16_14_10_13_1_2768 62 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 221 (accept_3_2 61 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 221 (Polychromatic418967fa.accept_16_12_10_13_1_1042 60 90
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 221 (accept_3_2 58 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 221 (Polychromatic418967fa.accept_20_17_10_1_1_11739 57 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 221 (Polychromatic418967fa.accept_21_14_6_11_1_7071 56 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 221 (accept_3_2 55 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 221
  (Polychromatic418967fa.accept_16_5_10_13_1_6042 53 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 221 (accept_3_2 52 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 221 (Polychromatic418967fa.accept_22_6_2_1_1_6763 50 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 221 (accept_3_2 49 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 221 (Polychromatic418967fa.accept_19_10_14_12_1_4795 48 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 221 (accept_3_2 46 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 221 (accept_3_2 43 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 221 (Polychromatic418967fa.accept_23_19_21_14_1_11548 42 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 221
  (Polychromatic418967fa.accept_21_20_6_11_1_2623 41 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 221 (accept_3_2 40 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 221 (accept_3_2 37 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 221 (accept_3_2 34 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 221 (accept_3_2 31 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 221
  (Polychromatic418967fa.accept_19_10_14_12_1_4795 29 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 90 221 (accept_3_2 28 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 221 (accept_3_2 25 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 221 (accept_3_2 22 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 221 (Polychromatic418967fa.accept_21_20_6_11_1_2623 20 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 221 (accept_3_2 19 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 221 (Polychromatic418967fa.accept_21_18_6_11_1_7031 18 90
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 221 (accept_3_2 16 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 221 (accept_3_2 13 90 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 221 (accept_3_2 10 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 221 (Polychromatic418967fa.accept_25_8_15_21_1_13130 8 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 221 (accept_3_2 7 90 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 221 (Polychromatic418967fa.accept_19_6_14_12_1_4811 6 90 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 221 (accept_3_2 4 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 221 (accept_3_2 1 90 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 221 (allA_succ_of_accept 88 89 221 (accept_3_2 88 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 89 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 89 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 221 (accept_3_2 85 89 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 221 (accept_3_2 82 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 221 (Polychromatic418967fa.accept_16_1_9_13_1_1822 81 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 80 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 221 (accept_3_2 79 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 89 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 221
  (Polychromatic418967fa.accept_19_1_13_12_1_7748 77 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 221 (accept_3_2 76 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 221 (accept_3_2 73 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 221 (accept_3_2 70 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 221 (accept_3_2 67 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 221 (accept_3_2 64 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 221 (accept_3_2 61 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 221
  (Polychromatic418967fa.accept_21_17_5_11_1_7028 59 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 221 (accept_3_2 58 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 221 (accept_3_2 55 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 221 (Polychromatic418967fa.accept_16_6_9_13_1_2751 54 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 221
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 53 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 221 (accept_3_2 52 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 221 (accept_3_2 49 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 221 (accept_3_2 46 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 221 (accept_3_2 43 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 221 (accept_3_2 40 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 221 (accept_3_2 37 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 221 (accept_3_2 34 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 221 (accept_3_2 31 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 221 (accept_3_2 28 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 26 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 221 (accept_3_2 25 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 221 (accept_3_2 22 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 221 (accept_3_2 19 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 221
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 221 (accept_3_2 16 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 221 (Polychromatic418967fa.accept_19_14_13_12_1_2259 14 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 221 (accept_3_2 13 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 221 (accept_3_2 10 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 221 (accept_3_2 7 89 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 221 (accept_3_2 4 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 89 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 221 (accept_3_2 1 89 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 221 (allA_of_3_0 88 88 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 221
  (allA_succ_of_accept 86 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 221 (accept_3_2 85 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 83
  87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 221 (accept_3_2 82 87
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 221
  (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 221 (accept_3_2 79 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199
  77 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 221 (accept_3_2 76
  87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 221
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 221 (accept_3_2 73 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 221 (Polychromatic418967fa.accept_22_6_21_1_1_13129 72 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 221 (accept_3_2 70 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 221 (accept_3_2 67 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 221 (accept_3_2 64 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 221 (accept_3_2 61 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 221
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 59 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 87 221 (accept_3_2 58 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 87 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 221 (accept_3_2 55 87 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 221 (accept_3_2 52 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 221 (Polychromatic418967fa.accept_19_13_11_12_1_3447 51 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 221 (accept_3_2 49 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 221 (accept_3_2 46 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 221 (accept_3_2 43 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 221 (accept_3_2 40 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 221 (accept_3_2 37 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 221 (accept_3_2 34 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 221 (accept_3_2 31 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 221 (accept_3_2 28 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 221 (accept_3_2 25 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 221
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 221 (accept_3_2 22 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 221 (accept_3_2 19 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 221 (accept_3_2 16 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 221 (accept_3_2 13 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 221 (accept_3_2 10 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 221 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 221 (accept_3_2 7 87 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 221
  (Polychromatic418967fa.accept_19_5_11_12_1_11765 5 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 221 (accept_3_2 4 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 221 (accept_3_2 1 87 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 221 (allA_succ_of_accept 85 86 221 (accept_3_2 85 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 221 (Polychromatic418967fa.accept_16_4_6_13_1_1874 84 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 221 (accept_3_2 82 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 221 (accept_3_2 79 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 221 (Polychromatic418967fa.accept_19_2_10_12_1_3446 78 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 77 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 221 (accept_3_2 76 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 221
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 74 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 86 221 (accept_3_2 73 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 86 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 221 (accept_3_2 70 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69
  86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 221 (accept_3_2 67 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 221 (Polychromatic418967fa.accept_19_9_10_12_1_6161 66 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 221 (accept_3_2 64 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 221 (accept_3_2 61 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 221 (Polychromatic418967fa.accept_19_3_10_12_1_6217 60 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 221 (accept_3_2 58 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 221 (accept_3_2 55 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 221 (Polychromatic418967fa.accept_22_9_20_1_1_13128 53 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 221 (accept_3_2 52 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 221
  (Polychromatic418967fa.accept_23_4_17_14_1_13127 50 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 86 221 (accept_3_2 49 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 86 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 221 (accept_3_2 46 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 221 (accept_3_2 43 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 221 (accept_3_2 40 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 221
  (Polychromatic418967fa.accept_21_17_2_11_1_8656 38 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 221 (accept_3_2 37 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 221 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 221 (accept_3_2 34 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 221 (accept_3_2 31 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 221 (Polychromatic418967fa.accept_19_11_10_12_1_2256 30 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 221 (accept_3_2 28 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 221 (accept_3_2 25 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 221 (Polychromatic418967fa.accept_25_24_11_21_1_9613 24 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 221 (accept_3_2 22 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 221 (accept_3_2 19 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 221 (Polychromatic418967fa.accept_22_18_20_1_1_11609 18 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 221 (accept_3_2 16 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 221
  (Polychromatic418967fa.accept_19_14_10_12_1_4809 14 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 221 (accept_3_2 13 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 221 (accept_3_2 10 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 221 (accept_3_2 7 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 221 (accept_3_2 4 86 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  86 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 221 (accept_3_2 1 86 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 221
  (allA_of_3_0 85 85 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 221 (allA_succ_of_accept 83 84 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 221 (accept_3_2 82 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 221 (accept_3_2 79 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 221
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 221 (accept_3_2 76 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 221 (accept_3_2 73 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 221 (accept_3_2 70 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 221 (Polychromatic418967fa.accept_19_11_8_12_1_6204 68 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 221 (accept_3_2 67 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 66 84 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 221 (accept_3_2 64 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 63 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 221 (accept_3_2 61 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 221
  (Polychromatic418967fa.accept_26_7_6_13_1_13126 59 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 221 (accept_3_2 58 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 221 (accept_3_2 55 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 221 (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 221 (accept_3_2 52 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 221 (accept_3_2 49 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 221 (Polychromatic418967fa.accept_19_10_8_12_1_7733 48 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 221 (accept_3_2 46 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 221 (accept_3_2 43 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 221 (accept_3_2 40 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 221 (accept_3_2 37 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 221 (accept_3_2 34 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 221 (accept_3_2 31 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 221 (Polychromatic418967fa.accept_19_11_8_12_1_6204 30 84
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 221 (accept_3_2 28 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 221 (accept_3_2 25 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 221
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 221 (accept_3_2 22 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 221 (accept_3_2 19 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 221 (Polychromatic418967fa.accept_24_18_12_5_1_13102 18 84 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 221 (accept_3_2 16 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 221 (Polychromatic418967fa.accept_22_14_18_1_1_13125 14 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 221 (accept_3_2 13 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 221 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 84
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 221 (accept_3_2 10 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 221 (accept_3_2 7 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 221 (accept_3_2 4 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  221 (Polychromatic418967fa.accept_20_3_4_1_1_11728 3 84 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 221 (accept_3_2 1 84 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 221
  (allA_succ_of_accept 82 83 221 (accept_3_2 82 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 221 (Polychromatic418967fa.accept_16_1_3_13_1_2785 81 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 221 (accept_3_2 79 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 221
  (Polychromatic418967fa.accept_19_1_7_12_1_3443 77 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 221 (accept_3_2 76 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 221 (accept_3_2 73 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 221 (accept_3_2 70 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 221 (accept_3_2 67 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 221 (accept_3_2 64 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 221 (accept_3_2 61 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 221 (accept_3_2 58 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 221 (Polychromatic418967fa.accept_16_8_3_13_1_7295 56 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 221 (accept_3_2 55 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 221 (accept_3_2 52 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 221 (accept_3_2 49 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 221 (accept_3_2 46 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 221 (accept_3_2 43 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 221
  (Polychromatic418967fa.accept_19_3_7_12_1_9105 41 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 221 (accept_3_2 40 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 221 (accept_3_2 37 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 221 (Polychromatic418967fa.accept_25_11_8_21_1_13124 36 83 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 221 (accept_3_2 34 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 221 (accept_3_2 31 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 221
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 221 (accept_3_2 28 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 221 (accept_3_2 25 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 221 (accept_3_2 22 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 221 (accept_3_2 19 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 221 (accept_3_2 16 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 221 (accept_3_2 13 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 221
  (Polychromatic418967fa.accept_19_11_7_12_1_4770 11 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 221 (accept_3_2 10 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 221 (accept_3_2 7 83 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 221 (accept_3_2 4 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 221 (accept_3_2 1 83 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 221 (allA_of_3_0 82 82 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 221
  (allA_succ_of_accept 80 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 221 (accept_3_2 79 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 221 (Polychromatic418967fa.accept_15_2_6_11_1_1587
  77 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 221 (accept_3_2 76
  81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 221
  (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 221 (accept_3_2 73 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 221 (Polychromatic418967fa.accept_19_15_5_12_1_13123 72 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 221
  (Polychromatic418967fa.accept_21_8_18_11_1_13121 71 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 81 221 (accept_3_2 70 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 81 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 221 (accept_3_2 67 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771
  66 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 221
  (Polychromatic418967fa.accept_15_5_6_11_1_854 65 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 221 (accept_3_2 64 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 221 (accept_3_2 61 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 221
  (Polychromatic418967fa.accept_39_20_3_26_1_13122 59 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 81 221 (accept_3_2 58 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 81 221 (Polychromatic418967fa.accept_16_9_1_13_1_1850 57 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 221 (accept_3_2 55 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586
  54 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 221
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 221 (accept_3_2 52 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 221 (accept_3_2 49 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 221 (accept_3_2 46 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 221 (Polychromatic418967fa.accept_19_7_5_12_1_7756 45 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 221 (accept_3_2 43 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 221 (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 221
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 221 (accept_3_2 40 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 221 (accept_3_2 37 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 221
  (Polychromatic418967fa.accept_15_5_6_11_1_854 35 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 221 (accept_3_2 34 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 221 (accept_3_2 31 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 221
  (Polychromatic418967fa.accept_21_8_18_11_1_13121 29 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 81 221 (accept_3_2 28 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 81 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 221 (accept_3_2 25 81 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586
  24 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 221
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 221 (accept_3_2 22 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 221 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 221 (accept_3_2 19 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 221 (accept_3_2 16 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 221 (accept_3_2 13 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 221
  (Polychromatic418967fa.accept_19_11_5_12_1_3439 11 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 221 (accept_3_2 10 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 221 (accept_3_2 7 81 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 221 (Polychromatic418967fa.accept_21_6_18_11_1_3960 6 81 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 221
  (Polychromatic418967fa.accept_15_5_6_11_1_854 5 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 221 (accept_3_2 4 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 221 (accept_3_2 1 81 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 221 (allA_succ_of_accept 79 80 221 (accept_3_2 79 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 80 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 77 80
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 221 (accept_3_2 76 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 221 (accept_3_2 73 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 221 (Polychromatic418967fa.accept_23_3_11_14_1_13120 72 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 221 (accept_3_2 70 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 221
  (Polychromatic418967fa.accept_11_2_3_1_1_244 68 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 221 (accept_3_2 67 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 221 (accept_3_2 64 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 221 (accept_3_2 61 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 221 (Polychromatic418967fa.accept_19_2_4_12_1_13084 59 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 221 (accept_3_2 58 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 221 (accept_3_2 55 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 221 (Polychromatic418967fa.accept_15_9_5_11_1_5416 54 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 221 (accept_3_2 52 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 221 (accept_3_2 49 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 221 (accept_3_2 46 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 221
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 44 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 221 (accept_3_2 43 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 221 (accept_3_2 40 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 221 (accept_3_2 37 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 221 (accept_3_2 34 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 221 (accept_3_2 31 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 221 (accept_3_2 28 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 221 (accept_3_2 25 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 221 (accept_3_2 22 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 221 (accept_3_2 19 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 221 (Polychromatic418967fa.accept_22_18_14_1_1_11642 18 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 221 (accept_3_2 16 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 221 (accept_3_2 13 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 221 (accept_3_2 10 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 221 (accept_3_2 7 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 221 (Polychromatic418967fa.accept_19_5_4_12_1_7773 5 80 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 221 (accept_3_2 4 80 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  80 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 221 (accept_3_2 1 80 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 221 (allA_of_3_0 79
  79 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 221 (allA_succ_of_accept 77 78 221
  (Polychromatic418967fa.accept_19_1_2_12_1_7725 77 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 221 (accept_3_2 76 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 221 (accept_3_2 73 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 221 (Polychromatic418967fa.accept_21_9_15_11_1_7018 72 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 221 (accept_3_2 70 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 221 (accept_3_2 67 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 78 221 13 5 6 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 78 221 (accept_3_2 64 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 78 221 (accept_3_2 61 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  78 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 60 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 221 (accept_3_2 58 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 78 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 221 (accept_3_2 55 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  78 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 78 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 221 13 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 221
  (Polychromatic418967fa.accept_29_21_20_18_1_13119 50 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 78 221 (accept_3_2 49 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 78 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 78 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 221 (accept_3_2 46 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 221 (accept_3_2 43 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  78 221 (Polychromatic418967fa.accept_16_10_14_13_1_1870 42 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 78 221 (Polychromatic418967fa.accept_19_3_2_12_1_13118 41 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 221 (accept_3_2 40 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 221 13 3 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 221 (accept_3_2 37 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 221 (Polychromatic418967fa.accept_15_6_3_11_1_848
  36 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 221 (accept_3_2 34 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 32 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 221 (accept_3_2 31 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 221 (accept_3_2 28 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 221 13 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 221 (accept_3_2 25 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 78 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 221 (accept_3_2 22 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 221 (accept_3_2 19 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  78 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 221 (accept_3_2 16 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 78 221 13 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 78 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 221 (accept_3_2 10 78 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9
  78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 221 (accept_3_2 7 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78
  221 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 78 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 221 (accept_3_2 4 78 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 221 (accept_3_2 1 78 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 221
  (allA_succ_of_accept 76 77 221 (accept_3_2 76 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 221 (Polychromatic418967fa.accept_19_18_1_12_1_6235 75 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 74 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 221 (accept_3_2 73 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 221 (Polychromatic418967fa.accept_27_18_23_5_1_5277 72 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 221
  (Polychromatic418967fa.accept_20_11_17_1_1_13117 71 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 77 221 (accept_3_2 70 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 77 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 69 77 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 68 77
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 221 (accept_3_2 67 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297
  66 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 221 (accept_3_2 64 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 221 (Polychromatic418967fa.accept_22_19_11_1_1_13116 63 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 221 (Polychromatic418967fa.accept_19_5_1_12_1_6102 62 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 221 (accept_3_2 61 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 221 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 221
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 221 (accept_3_2 58 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 221 (Polychromatic418967fa.accept_25_7_2_21_1_13115 57 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 221 (accept_3_2 55 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 221
  (Polychromatic418967fa.accept_26_1_25_13_1_13114 53 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 77 221 (accept_3_2 52 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 77 221 (Polychromatic418967fa.accept_15_6_2_11_1_325 51 77 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 50 77
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 221 (accept_3_2 49 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 221
  (Polychromatic418967fa.accept_21_6_14_11_1_10103 48 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 221 (Polychromatic418967fa.accept_19_9_1_12_1_6234 47 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 221 (accept_3_2 46 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 221
  (Polychromatic418967fa.accept_10_4_7_1_1_471 44 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 221 (accept_3_2 43 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  77 221 (Polychromatic418967fa.accept_19_4_1_12_1_4803 42 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 77 221 (Polychromatic418967fa.accept_21_20_14_11_1_13099 41 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 221 (accept_3_2 40 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 77
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 221
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 38 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 221 (accept_3_2 37 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 221 (accept_3_2 34 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 221 (Polychromatic418967fa.accept_21_12_14_11_1_3921 33 77
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 221
  (Polychromatic418967fa.accept_14_4_7_11_1_790 32 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 221 (accept_3_2 31 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 30 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 221 (Polychromatic418967fa.accept_21_8_14_11_1_11676 29 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 221 (accept_3_2 28 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 221 (Polychromatic418967fa.accept_19_8_1_12_1_4804 27 77
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 221
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 221 (accept_3_2 25 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 221 (Polychromatic418967fa.accept_19_4_1_12_1_4803 23 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 221 (accept_3_2 22 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 221 (Polychromatic418967fa.accept_15_6_2_11_1_325 21 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 221 (accept_3_2 19 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 221 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 221 (accept_3_2 16 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 221 (Polychromatic418967fa.accept_22_15_11_1_1_6777 15 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 221
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 221 (accept_3_2 13 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 221 (Polychromatic418967fa.accept_21_12_14_11_1_3921 12 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 221 (accept_3_2 10 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 77 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 221
  (Polychromatic418967fa.accept_19_8_1_12_1_4804 8 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 221 (accept_3_2 7 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 221 (accept_3_2 4 77 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 77 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 221
  (Polychromatic418967fa.accept_19_2_1_12_1_9092 2 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 221 (accept_3_2 1 77 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 221 (allA_of_3_0 76 76
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 221 (allA_succ_of_accept 74 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 221 (accept_3_2 73 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 221 (accept_3_2 70 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 221 (accept_3_2 67 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 221 (accept_3_2 64 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 221 (Polychromatic418967fa.accept_19_6_18_12_1_6125 63 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 221 (accept_3_2 61 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 221 (accept_3_2 58 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 221 (accept_3_2 55 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 221 (accept_3_2 52 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 221 (accept_3_2 49 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 221 (accept_3_2 46 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 221 (accept_3_2 43 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 221 (accept_3_2 40 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 221 (accept_3_2 37 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 221 (accept_3_2 34 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 221 (accept_3_2 31 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 221 (accept_3_2 28 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 221 (accept_3_2 25 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 221 (accept_3_2 22 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 221 (accept_3_2 19 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 221 (accept_3_2 16 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 221 (accept_3_2 13 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 221 (Polychromatic418967fa.accept_22_12_9_1_1_13113 12 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 221 (accept_3_2 10 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 221 (accept_3_2 7 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 221 (Polychromatic418967fa.accept_20_5_15_1_1_7278 5 75 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 221 (accept_3_2 4 75 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 221 (Polychromatic418967fa.accept_21_3_12_11_1_7034 3 75 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 221 (accept_3_2 1 75 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 221 (allA_succ_of_accept
  73 74 221 (accept_3_2 73 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 221
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 221 (accept_3_2 70 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 221 (accept_3_2 67 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 65 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 221 (accept_3_2 64 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 221 (accept_3_2 61 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 221 (accept_3_2 58 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 221 (accept_3_2 55 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 221 (Polychromatic418967fa.accept_23_8_5_14_1_13112 54 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 221 (accept_3_2 52 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 221 (accept_3_2 49 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 221 (accept_3_2 46 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 221 (accept_3_2 43 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 221 (Polychromatic418967fa.accept_19_3_17_12_1_6176 41 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 221 (accept_3_2 40 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 221
  (Polychromatic418967fa.accept_23_15_5_14_1_11592 38 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 74 221 (accept_3_2 37 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 74 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 74 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 221 (accept_3_2 34 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 221 (accept_3_2 31 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 221 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 221 (accept_3_2 28 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 221 (accept_3_2 25 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 221 (accept_3_2 22 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 221 (accept_3_2 19 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 221 (accept_3_2 16 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 221
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 221 (accept_3_2 13 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 74 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 221 (accept_3_2 10 74 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 221 (accept_3_2 7 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 74 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 221 (accept_3_2 4 74 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 221 (Polychromatic418967fa.accept_19_2_17_12_1_6097
  2 74 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 221 (accept_3_2 1 74
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 221 (allA_of_3_0 73 73 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 221 (allA_succ_of_accept 71 72 221
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 221 (accept_3_2 70 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 221 (accept_3_2 67 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 221
  (Polychromatic418967fa.accept_14_9_2_11_1_780 65 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 221 (accept_3_2 64 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 221 (accept_3_2 61 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 221
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 221 (accept_3_2 58 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 221 (Polychromatic418967fa.accept_21_15_9_11_1_5417 57 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 221 (accept_3_2 55 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 221
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 221 (accept_3_2 52 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 221 (Polychromatic418967fa.accept_26_24_20_13_1_13111 50 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 221 (accept_3_2 49 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 72 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 221 (accept_3_2 46 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 221 (Polychromatic418967fa.accept_19_7_15_12_1_4800 45 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 221 (accept_3_2 43 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 221 (Polychromatic418967fa.accept_25_17_22_21_1_13110 42 72
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 221 (accept_3_2 40 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 221 (accept_3_2 37 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 221
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 35 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 221 (accept_3_2 34 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 221 (Polychromatic418967fa.accept_23_9_3_14_1_6455 32 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 221 (accept_3_2 31 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 221 (Polychromatic418967fa.accept_23_7_3_14_1_13109 30 72
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 221
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 221 (accept_3_2 28 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 221 (accept_3_2 25 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 221 (Polychromatic418967fa.accept_19_5_15_12_1_6273 24 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 221
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 221 (accept_3_2 22 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 221 (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 221 (accept_3_2 19 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 221
  (Polychromatic418967fa.accept_19_17_15_12_1_10534 17 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 72 221 (accept_3_2 16 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 72 221 (Polychromatic418967fa.accept_21_15_9_11_1_5417 15 72 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 72
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 221 (accept_3_2 13 72 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 221
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 221 (accept_3_2 10 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 221 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 221 (accept_3_2 7 72 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 221 (accept_3_2 4 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  221 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 221 (Polychromatic418967fa.accept_21_2_9_11_1_13096 2 72 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 221 (accept_3_2 1 72 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 221
  (allA_succ_of_accept 70 71 221 (accept_3_2 70 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 221 (accept_3_2 67 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 221 (accept_3_2 64 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 221 (Polychromatic418967fa.accept_19_6_14_12_1_4811 63 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 221 (accept_3_2 61 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 221 (accept_3_2 58 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 221 (accept_3_2 55 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 221
  (Polychromatic418967fa.accept_22_9_5_1_1_2204 53 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 221 (accept_3_2 52 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 221 (accept_3_2 49 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 221 (accept_3_2 46 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 44 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 221 (accept_3_2 43 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 221
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 41 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 221 (accept_3_2 40 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 221 (accept_3_2 37 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 221 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 221
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 35 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 71 221 (accept_3_2 34 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 71 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 32 71
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 221 (accept_3_2 31 71 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 221 (accept_3_2 28 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 221 (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 221 (accept_3_2 25 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 221
  (Polychromatic418967fa.accept_27_23_17_5_1_13108 23 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 71 221 (accept_3_2 22 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 71 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 221 (accept_3_2 19 71 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 221 (accept_3_2 16 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 221 (accept_3_2 13 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 221 (accept_3_2 10 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 221 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 8 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 221 (accept_3_2 7 71 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 221 (accept_3_2 4 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 221 (accept_3_2 1 71 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 221
  (allA_of_3_0 70 70 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 221 (allA_succ_of_accept 68 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 221 (accept_3_2 67 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 221 (accept_3_2 64 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 221 (accept_3_2 61 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 221 (accept_3_2 58 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 221 (accept_3_2 55 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 221 (accept_3_2 52 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 221 (accept_3_2 49 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 221 (accept_3_2 46 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 221 (accept_3_2 43 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 221 (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 221 (accept_3_2 40 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 221 (accept_3_2 37 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 221 (accept_3_2 34 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 221 (accept_3_2 31 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 221 (accept_3_2 28 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 221 (accept_3_2 25 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 221 (accept_3_2 22 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 221 (accept_3_2 19 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 221 (accept_3_2 16 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 221 (accept_3_2 13 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 221 (accept_3_2 10 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 221 (accept_3_2 7 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  221 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 221 (accept_3_2 4 69 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 221 (accept_3_2 1 69 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 221 (allA_succ_of_accept 67 68
  221 (accept_3_2 67 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 221
  (Polychromatic418967fa.accept_25_16_18_21_1_13107 66 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 221 (accept_3_2 64 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 221 (accept_3_2 61 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 221 (Polychromatic418967fa.accept_16_12_4_13_1_3827 60 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 221 (accept_3_2 58 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 221
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 221 (accept_3_2 55 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 221 (accept_3_2 52 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 51 68 221 17 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 68 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 221 (accept_3_2 49 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 221
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 68 221 (accept_3_2 46 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 68 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 221 (accept_3_2 43 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 68 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 68 221 (accept_3_2 40 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 68 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 221 (accept_3_2 37 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 68 221 17 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 68
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 221 (accept_3_2 31 68 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 221 (accept_3_2 28 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 221 (accept_3_2 25 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 221 (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 221 (accept_3_2 22 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 221 (accept_3_2 19 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 68 221 17 1 4 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 68 221 (accept_3_2 16 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 221
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 221 (accept_3_2 13 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 221 (accept_3_2 10 68 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 221 (accept_3_2 7 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 68 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 221 (accept_3_2 4 68 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 221 (accept_3_2 1 68 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 221 (allA_of_3_0 67 67 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 221 (allA_succ_of_accept 65 66 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 221 (accept_3_2 64 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 221 (accept_3_2 61 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 221 (accept_3_2 58 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 221 (accept_3_2 55 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 221 (accept_3_2 52 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 221 (accept_3_2 49 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 221 (accept_3_2 46 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 221 (accept_3_2 43 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 221 (accept_3_2 40 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 221 (accept_3_2 37 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 221 (accept_3_2 34 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 221 (accept_3_2 31 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 221 (Polychromatic418967fa.accept_23_7_20_14_1_11501 30 66 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 221 (accept_3_2 28 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 221 (accept_3_2 25 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 221 (accept_3_2 22 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 21 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 221 (accept_3_2 19 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 221 (accept_3_2 16 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 221 (Polychromatic418967fa.accept_19_14_9_12_1_9113 14 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 221 (accept_3_2 13 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 221 (accept_3_2 10 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 221 (accept_3_2 7 66 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 221 (accept_3_2 4 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 66 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 221 (accept_3_2 1 66 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 221
  (allA_succ_of_accept 64 65 221 (accept_3_2 64 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 221 (Polychromatic418967fa.accept_19_6_8_12_1_6271 63 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 221 (accept_3_2 61 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 221 (accept_3_2 58 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 221 (accept_3_2 55 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 65 221 13 4 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 65 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 65 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 50 65
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 221 (accept_3_2 49 65 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 221 (accept_3_2 46 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 221 (Polychromatic418967fa.accept_19_7_8_12_1_9107 45 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 221 (accept_3_2 43 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 221 (accept_3_2 40 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 65
  221 13 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38
  65 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 65 221 (accept_3_2 37 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 65 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 221 (accept_3_2 34 65 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 221 (accept_3_2 31 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 221 (accept_3_2 28 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 221 13 2 5 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 65 221 (accept_3_2 25 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 221 (accept_3_2 22 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 221 (accept_3_2 19 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 221 (Polychromatic418967fa.accept_23_18_19_14_1_1759 18 65 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 221 (accept_3_2 16 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 221 13 1 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 221
  (Polychromatic418967fa.accept_19_11_8_12_1_6204 11 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 221 (accept_3_2 10 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 221 (accept_3_2 7 65 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 221 (accept_3_2 4 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 65 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 65 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 221 (accept_3_2 1 65 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 221
  (allA_of_3_0 64 64 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 221 (allA_succ_of_accept 62 63 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 221 (accept_3_2 61 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 221 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 221 (accept_3_2 58 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 221 (accept_3_2 55 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 221 (Polychromatic418967fa.accept_15_8_3_11_1_849 53 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 221 (accept_3_2 52 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 221 (accept_3_2 49 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 221 (Polychromatic418967fa.accept_24_23_15_5_1_7963 47 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 221 (accept_3_2 46 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 221 (accept_3_2 43 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 221 (Polychromatic418967fa.accept_26_15_11_13_1_13106 41 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 221 (accept_3_2 40 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 221 (Polychromatic418967fa.accept_25_14_13_21_1_13091 39 63
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 221 (accept_3_2 37 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 221 (Polychromatic418967fa.accept_16_3_15_13_1_2825 35 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 221 (accept_3_2 34 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 221 (accept_3_2 31 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 221 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 221 (accept_3_2 28 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 221 (Polychromatic418967fa.accept_19_8_6_12_1_13105 27 63
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 221 (accept_3_2 25 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 221 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 221 (Polychromatic418967fa.accept_15_8_3_11_1_849 23 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 221 (accept_3_2 22 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 221 (accept_3_2 19 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 221 (accept_3_2 16 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 221 (accept_3_2 13 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 221 (Polychromatic418967fa.accept_22_11_19_1_1_8415 11 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 221 (accept_3_2 10 63 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 221 (accept_3_2 7 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 221 (Polychromatic418967fa.accept_20_5_3_1_1_10415 5 63 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 221 (accept_3_2 4 63 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 63 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 221 (accept_3_2 1 63 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 221 (allA_succ_of_accept 61 62 221
  (accept_3_2 61 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 60 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 221 (accept_3_2 58 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 221 (accept_3_2 55 62
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 221 (accept_3_2 52 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 221 (Polychromatic418967fa.accept_11_6_7_1_1_564
  50 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 221 (accept_3_2 49
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 221 (accept_3_2 46 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 221 (accept_3_2 43 62
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 221 (Polychromatic418967fa.accept_22_19_18_1_1_13104 41 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 221 (accept_3_2 40 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 221 (accept_3_2 37 62
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 221 (accept_3_2 34 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 221 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 221 (accept_3_2 31
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 221 (accept_3_2 28 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 221 (accept_3_2 25 62
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 221 (Polychromatic418967fa.accept_7_3_6_4_1_30
  24 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 221 (accept_3_2 22 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 221 (accept_3_2 19 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 221 (Polychromatic418967fa.accept_21_18_20_11_1_3927 18 62 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 221 (accept_3_2 16 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 221 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 221 (accept_3_2 13 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 221 (accept_3_2 10 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 221 (accept_3_2 7 62 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 221 (accept_3_2 4 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 221 (accept_3_2 1 62 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 221
  (allA_of_3_0 61 61 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 221 (allA_succ_of_accept 59 60 221
  (Polychromatic418967fa.accept_19_2_3_12_1_10559 59 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 221 (accept_3_2 58 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 221 (accept_3_2 55 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 221 (Polychromatic418967fa.accept_21_12_18_11_1_10051 54 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 221 (accept_3_2 52 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 221 (Polychromatic418967fa.accept_18_15_6_5_1_3972 51 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 221 (accept_3_2 49 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 221 (accept_3_2 46 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 221 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 221 (accept_3_2 43 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 221 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 221 (accept_3_2 40 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 221 (accept_3_2 37 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 221 (accept_3_2 34 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 221 (Polychromatic418967fa.accept_19_13_3_12_1_6186 32 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 221 (accept_3_2 31 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 221 (accept_3_2 28 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 221 (Polychromatic418967fa.accept_21_6_18_11_1_3960 27 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 221 (accept_3_2 25 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 221
  (Polychromatic418967fa.accept_25_23_10_21_1_13103 23 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 60 221 (accept_3_2 22 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 221 (accept_3_2 19 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 221
  (Polychromatic418967fa.accept_24_18_12_5_1_13102 18 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 60 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 221 (accept_3_2 16 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 221 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 60 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 221
  (Polychromatic418967fa.accept_21_14_18_11_1_3961 14 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 221 (accept_3_2 13 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 60 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 221 (accept_3_2 10 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 221 (accept_3_2 7 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60
  221 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 221 (Polychromatic418967fa.accept_21_5_18_11_1_7041 5 60 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 221 (accept_3_2 4 60 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  60 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 221 (accept_3_2 1 60 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 221 (allA_succ_of_accept 58 59 221 (accept_3_2 58 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 221 (Polychromatic418967fa.accept_16_8_11_13_1_7265 56 59
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 221 (accept_3_2 55 59 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 221
  (Polychromatic418967fa.accept_22_9_15_1_1_13101 53 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 221 (accept_3_2 52 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 221 (Polychromatic418967fa.accept_23_5_13_14_1_13100 51 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 221 (accept_3_2 49 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 221
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 221 (accept_3_2 46 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 221 (Polychromatic418967fa.accept_19_6_2_12_1_6136 44 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 221 (accept_3_2 43 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 221 (accept_3_2 40 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 221 (Polychromatic418967fa.accept_19_1_2_12_1_7725 39 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 221 (accept_3_2 37 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 221 (accept_3_2 34 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 33 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 221 (accept_3_2 31 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 221 (accept_3_2 28 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 221 (accept_3_2 25 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 221 (Polychromatic418967fa.accept_16_8_11_13_1_7265 24 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 221
  (Polychromatic418967fa.accept_19_4_2_12_1_10527 23 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 221 (accept_3_2 22 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 221 (accept_3_2 19 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 221
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 17 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 221 (accept_3_2 16 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 221 (accept_3_2 13 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 221
  (Polychromatic418967fa.accept_22_11_15_1_1_8397 11 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 221 (accept_3_2 10 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 221 (Polychromatic418967fa.accept_19_9_2_12_1_6243 9 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 221 (accept_3_2 7 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 221 (accept_3_2 4 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 59 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 221 (accept_3_2 1 59 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 221
  (allA_of_3_0 58 58 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 221 (allA_succ_of_accept 56 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 221 (accept_3_2 55 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 221 (accept_3_2 52 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 221 (accept_3_2 49 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 221 (Polychromatic418967fa.accept_21_6_15_11_1_5410 48 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 221 (accept_3_2 46 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 221 (accept_3_2 43 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 221 (Polychromatic418967fa.accept_24_17_9_5_1_7985 41 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 221 (accept_3_2 40 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 221 (accept_3_2 37 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 221 (accept_3_2 34 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 221 (accept_3_2 31 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 221 (Polychromatic418967fa.accept_20_10_17_1_1_8852 30 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 221 (accept_3_2 28 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 221 (accept_3_2 25 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 221 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 221 (accept_3_2 22 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 221 (accept_3_2 19 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 221 (accept_3_2 16 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 221 (accept_3_2 13 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 221 (accept_3_2 10 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 221 (Polychromatic418967fa.accept_21_9_15_11_1_7018 9 57 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 221 (accept_3_2 7 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 221 (accept_3_2 4 57 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 221 (accept_3_2 1 57 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 221 (allA_succ_of_accept 55 56 221 (accept_3_2 55 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 221 (Polychromatic418967fa.accept_21_12_14_11_1_3921 54 56 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 221 (accept_3_2 52 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 221 (accept_3_2 49 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 221 (accept_3_2 46 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 221 (accept_3_2 43 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 221 (Polychromatic418967fa.accept_21_20_14_11_1_13099 41 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 221 (accept_3_2 40 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 221 (accept_3_2 37 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 221 (accept_3_2 34 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 221 (accept_3_2 31 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 221 (Polychromatic418967fa.accept_21_8_14_11_1_11676 29 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 221 (accept_3_2 28 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 221 (accept_3_2 25 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 221 (Polychromatic418967fa.accept_21_2_14_11_1_7060 23 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 221 (accept_3_2 22 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 221
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 221 (accept_3_2 19 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 221 (Polychromatic418967fa.accept_20_18_16_1_1_8850 18 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 221 (accept_3_2 16 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 221 (accept_3_2 13 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 221 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 221 (accept_3_2 10 56 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 221 (accept_3_2 7 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 56 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 221 (accept_3_2 4 56 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 221 (accept_3_2 1 56 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 221 (allA_of_3_0 55 55 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 221
  (allA_succ_of_accept 53 54 221 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 221 (accept_3_2 52 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 221 (accept_3_2 49 54
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 221 (accept_3_2 46 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 221 (accept_3_2 43 54
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 221
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 221 (accept_3_2 40 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 221 (Polychromatic418967fa.accept_24_14_6_5_1_7999
  38 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 221 (accept_3_2 37
  54 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 221 (accept_3_2 34 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 221 (Polychromatic418967fa.accept_19_14_16_12_1_13098 33 54 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 221
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 221 (accept_3_2 31 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 221 (accept_3_2 28 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 221
  (Polychromatic418967fa.accept_19_7_16_12_1_10556 26 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 54 221 (accept_3_2 25 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 54 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 221 (accept_3_2 22 54 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 221 (Polychromatic418967fa.accept_15_6_9_11_1_858
  21 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 221 (accept_3_2 19 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 221 (Polychromatic418967fa.accept_21_18_12_11_1_7078 18 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 221 (accept_3_2 16 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 221
  (Polychromatic418967fa.accept_19_14_16_12_1_13098 14 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 54 221 (accept_3_2 13 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 54 221 (Polychromatic418967fa.accept_24_12_6_5_1_13097 12 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 221 (accept_3_2 10 54 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 221 (accept_3_2 7 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 221 (accept_3_2 4 54 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  54 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 221 (accept_3_2 1 54 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 221))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 221 (allA_succ_of_accept 52 53 221 (accept_3_2 52 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 53 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 50 53
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 221 (accept_3_2 49 53 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48
  53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 221 (accept_3_2 46 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 221 (Polychromatic418967fa.accept_19_7_15_12_1_4800 45 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 44 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 221 (accept_3_2 43 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 221
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 221 (accept_3_2 40 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 221 (accept_3_2 37 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 221 (Polychromatic418967fa.accept_19_17_15_12_1_10534 36 53 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 221 (accept_3_2 34 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 221 (accept_3_2 31 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 221 (accept_3_2 28 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 221 (Polychromatic418967fa.accept_16_10_5_13_1_8591 26 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 221 (accept_3_2 25 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 221
  (Polychromatic418967fa.accept_20_3_13_1_1_8886 23 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 221 (accept_3_2 22 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 221 (accept_3_2 19 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 221
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 221 (accept_3_2 16 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 221 (Polychromatic418967fa.accept_20_14_13_1_1_8844 14 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 221 (accept_3_2 13 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 221 (accept_3_2 10 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 221 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 221 (accept_3_2 7 53 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 221 (accept_3_2 4 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 221 (accept_3_2 1 53 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 221))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 221 (allA_of_3_0 52 52
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 221 (allA_succ_of_accept 50 51 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 221 (accept_3_2 49 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 221 (accept_3_2 46 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 221 (accept_3_2 43 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 221 (accept_3_2 40 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 221 (accept_3_2 37 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 221 (Polychromatic418967fa.accept_20_16_11_1_1_10407 36 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 221 17 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 51 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 221 (accept_3_2 31 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 221 (accept_3_2 28 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 221 (accept_3_2 25 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 221 (Polychromatic418967fa.accept_21_2_9_11_1_13096 23 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 221 (accept_3_2 22 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 221 (accept_3_2 19 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 51 221 17 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 51 221 (accept_3_2 16 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 51 221 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 51 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 221 (accept_3_2 13 51 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 221 (accept_3_2 10 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 221 (accept_3_2 7 51 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 221 (accept_3_2 4 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 221 (accept_3_2 1 51 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 221))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 221 (allA_succ_of_accept
  49 50 221 (accept_3_2 49 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 221
  (Polychromatic418967fa.accept_23_2_4_14_1_13095 48 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 221 (accept_3_2 46 50 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 221 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 221 (accept_3_2 43
  50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 221
  (Polychromatic418967fa.accept_23_19_4_14_1_13094 42 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 221 (Polychromatic418967fa.accept_21_20_8_11_1_5407 41 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 221 (accept_3_2 40 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 221 (accept_3_2 37 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 221 (accept_3_2 34 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 221 (accept_3_2 31 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 221 (Polychromatic418967fa.accept_23_7_4_14_1_11574 30 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 221 (accept_3_2 28 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 221 (accept_3_2 25 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 221 (accept_3_2 22 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 221 (accept_3_2 19 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 221 (accept_3_2 16 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 221
  (Polychromatic418967fa.accept_20_14_10_1_1_13086 14 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 50 221 (accept_3_2 13 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 50 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 221 (accept_3_2 10 50 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 221 (accept_3_2 7 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 50 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 221 (accept_3_2 4 50 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 221 (accept_3_2 1 50 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  221)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 221 (allA_of_3_0 49 49 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 221 (allA_succ_of_accept 47 48 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 221 (accept_3_2 46 48
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 221 (Polychromatic418967fa.accept_7_3_6_4_1_30
  45 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 221 (accept_3_2 43 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  48 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 48 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 221 (accept_3_2 40 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 221 (accept_3_2 37 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  48 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 48 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 221 (accept_3_2 34 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 221
  (Polychromatic418967fa.accept_25_7_23_21_1_13093 32 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 221 (accept_3_2 31 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 48 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 48 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 221 (accept_3_2 28 48 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 221 (Polychromatic418967fa.accept_18_9_12_5_1_864
  27 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 221 (accept_3_2 25 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  48 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 48 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 221 (accept_3_2 22 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 48 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 221 (accept_3_2 19 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  48 221 (Polychromatic418967fa.accept_20_18_8_1_1_10382 18 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 48 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 221 (accept_3_2 16 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 221 (accept_3_2 13 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  48 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 48 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 221 (accept_3_2 10 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 221 (accept_3_2 7 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48
  221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 221 (accept_3_2 4 48 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 221 (accept_3_2 1 48 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 221)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 221 (allA_succ_of_accept 46 47 221 (accept_3_2 46 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 221 (Polychromatic418967fa.accept_24_21_23_5_1_13092 45 47 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 221 (accept_3_2 43 47 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 221 (accept_3_2 40 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 221 (accept_3_2 37 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 221 (accept_3_2 34 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 32 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 221 (accept_3_2 31 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 221 (accept_3_2 28 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 221 (accept_3_2 25 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 221 (accept_3_2 22 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 221 (accept_3_2 19 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 221 (accept_3_2 16 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 221 (accept_3_2 13 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 221
  (Polychromatic418967fa.accept_20_11_7_1_1_8874 11 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 221 (accept_3_2 10 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 221 (accept_3_2 7 47 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 221 (accept_3_2 4 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 221 (accept_3_2 1 47 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 221))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 221 (allA_of_3_0 46 46 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 221 (allA_succ_of_accept 44 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 221 (accept_3_2 43 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 221 (Polychromatic418967fa.accept_19_4_7_12_1_6201 42 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 221 (accept_3_2 40 45 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 221 (accept_3_2 37 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 221 (accept_3_2 34 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 221 (Polychromatic418967fa.accept_18_15_9_5_1_3934 33 45
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 221 (accept_3_2 31 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 221 (accept_3_2 28 45 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 221 (accept_3_2 25 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 221 (Polychromatic418967fa.accept_19_4_7_12_1_6201 23 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 221 (accept_3_2 22 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 45
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 221 (accept_3_2 19 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 221 (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 221 (Polychromatic418967fa.accept_24_17_21_5_1_11439 17 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 221 (accept_3_2 16 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 221 (accept_3_2 13 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 221 (Polychromatic418967fa.accept_19_11_7_12_1_4770 11 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 221 (accept_3_2 10 45 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 221 (accept_3_2 7 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 221 (Polychromatic418967fa.accept_19_5_7_12_1_2252 5 45 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 221 (accept_3_2 4 45 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 221 (accept_3_2 1 45 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 221))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  221 (allA_succ_of_accept 43 44 221 (accept_3_2 43 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 221 (accept_3_2 40 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 221 (accept_3_2 37 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 221 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 221 (accept_3_2 34 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 221
  (Polychromatic418967fa.accept_18_14_8_5_1_860 32 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 221 (accept_3_2 31 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 221 (accept_3_2 28 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 221 (accept_3_2 25 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 221 (Polychromatic418967fa.accept_14_9_2_11_1_780 23 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 221 (accept_3_2 22 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 221 (accept_3_2 19 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 221 (accept_3_2 16 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 221 (accept_3_2 13 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 221 (accept_3_2 10 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 221
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 221 (accept_3_2 7 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 221 (accept_3_2 4 44 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  44 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 221 (accept_3_2 1 44 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 221)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  221 (allA_of_3_0 43 43 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 221 (allA_succ_of_accept 41 42 221
  (Polychromatic418967fa.accept_22_19_20_1_1_6783 41 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 221 (accept_3_2 40 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 221 (accept_3_2 37 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 221 (accept_3_2 34 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 221 (accept_3_2 31 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 221 (accept_3_2 28 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 221 (accept_3_2 25 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 221 (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 221 (accept_3_2 22 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 221 (accept_3_2 19 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 221 (Polychromatic418967fa.accept_22_18_20_1_1_11609 18 42 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 221 (accept_3_2 16 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 221 (accept_3_2 13 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 221 (accept_3_2 10 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 221 (accept_3_2 7 42 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 221
  (Polychromatic418967fa.accept_16_5_10_13_1_6042 5 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 221 (accept_3_2 4 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 221 (accept_3_2 1 42 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 221)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 221 (allA_succ_of_accept 40 41
  221 (accept_3_2 40 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 221
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 39 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 221 (accept_3_2 37 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 221
  (Polychromatic418967fa.accept_21_14_20_11_1_8630 35 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 41 221 (accept_3_2 34 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 41 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 221 (Polychromatic418967fa.accept_19_13_3_12_1_6186 32 41
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 221 (accept_3_2 31 41 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 221
  (Polychromatic418967fa.accept_19_10_3_12_1_10566 29 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 41 221 (accept_3_2 28 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 41 221 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 221 (accept_3_2 25 41 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 221 (accept_3_2 22 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 221 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 221 (accept_3_2 19 41 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 221 (Polychromatic418967fa.accept_21_18_20_11_1_3927 18 41 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 221 (accept_3_2 16 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 221 (Polychromatic418967fa.accept_21_14_20_11_1_8630 14 41 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 221 (accept_3_2 13 41 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 221
  (Polychromatic418967fa.accept_19_11_3_12_1_6138 11 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 221 (accept_3_2 10 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 221 (Polychromatic418967fa.accept_21_8_20_11_1_7025 8 41 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 221 (accept_3_2 7 41 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 221 (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 41 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 221 (accept_3_2 4 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 221 (accept_3_2 1 41 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 221))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 221 (allA_of_3_0 40 40 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 221 (allA_succ_of_accept 38 39 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 221 (accept_3_2 37 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 221 (accept_3_2 34 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 221 (accept_3_2 31 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 221 (accept_3_2 28 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 39 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 221 13 2 3 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 221 (accept_3_2 25 39 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 221
  (Polychromatic418967fa.accept_19_4_1_12_1_4803 23 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 221 (accept_3_2 22 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 221 (accept_3_2 19 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 221 (accept_3_2 16 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 221 13 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 12
  39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 221 (accept_3_2 10 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 39 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 221 (accept_3_2 7 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 221 (accept_3_2 4 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39
  221 (Polychromatic418967fa.accept_21_3_18_11_1_10061 3 39 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 39 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 221 (accept_3_2 1 39 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 39 221))))))))))))))))))))))))))))))))))))))) (allB_succ 38 221 (allA_succ_of_accept 37
  38 221 (accept_3_2 37 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 221 (accept_3_2 34 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 221 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 221 (accept_3_2 31
  38 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 221
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 221 (accept_3_2 28 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 26
  38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 221 (accept_3_2 25 38
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 221
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 221 (accept_3_2 22 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20
  38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 221 (accept_3_2 19 38
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 221
  (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 38 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 221 (accept_3_2 16 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 221
  (Polychromatic418967fa.accept_25_14_13_21_1_13091 14 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 38 221 (accept_3_2 13 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 38 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 221 (accept_3_2 10 38 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 221 (accept_3_2 7 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 221 (accept_3_2 4 38 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 221 (Polychromatic418967fa.accept_21_2_17_11_1_7037
  2 38 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 221 (accept_3_2 1 38
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 221)))))))))))))))))))))))))))))))))))))) (allB_succ 37 221
  (allA_of_3_0 37 37 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 221 (allA_succ_of_accept 35 36 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 221 (accept_3_2 34 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 221 (accept_3_2 31 36 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 221 (Polychromatic418967fa.accept_21_9_15_11_1_7018 30 36 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 221
  (Polychromatic418967fa.accept_19_10_17_12_1_2271 29 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 36 221 (accept_3_2 28 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 36 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 221 (accept_3_2 25 36 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 221
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 221 (accept_3_2 22 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 221 (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 221 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 36 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 221 (accept_3_2 19 36 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 36 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 221 (accept_3_2 16 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 221 (Polychromatic418967fa.accept_19_14_17_12_1_6099 14 36 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 221 (accept_3_2 13 36 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 221
  (Polychromatic418967fa.accept_20_11_16_1_1_13090 11 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 36 221 (accept_3_2 10 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 36 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 221 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 36 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 221 (accept_3_2 7 36 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 221 (Polychromatic418967fa.accept_16_6_4_13_1_3841
  6 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 221 (accept_3_2 4 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 221 (accept_3_2 1 36 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 221)))))))))))))))))))))))))))))))))))) (allB_succ 35 221 (allA_succ_of_accept 34 35 221
  (accept_3_2 34 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 221 (accept_3_2 31 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 221 (accept_3_2 28 35
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 221
  (Polychromatic418967fa.accept_20_7_15_1_1_13089 27 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 221 (accept_3_2 25 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358
  23 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 221 (accept_3_2 22
  35 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 221 (accept_3_2 19 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 221 (Polychromatic418967fa.accept_14_3_7_11_1_765
  17 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 221 (accept_3_2 16
  35 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 221 (accept_3_2 13 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 221 (accept_3_2 10 35
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 221 (accept_3_2 7 35 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 221 (Polychromatic418967fa.accept_19_5_16_12_1_6175
  5 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 221 (accept_3_2 4 35
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 221 (Polychromatic418967fa.accept_9_3_8_5_1_65
  3 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 221 (accept_3_2 1 35 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  221))))))))))))))))))))))))))))))))))) (allB_succ 34 221 (allA_of_3_0 34 34 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 221 (allA_succ_of_accept 32 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 221 (accept_3_2 31 33 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 221 (accept_3_2 28 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 221 (accept_3_2 25 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 24 33 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 221 (accept_3_2 22 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 221 (accept_3_2 19 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 33 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 221 (accept_3_2 16 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 221 (accept_3_2 13 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 221 (accept_3_2 10 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 221 (accept_3_2 7 33 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 221
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 221 (accept_3_2 4 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 221 (accept_3_2 1 33 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 221))))))))))))))))))))))))))))))))) (allB_succ 32 221 (allA_succ_of_accept 31 32 221
  (accept_3_2 31 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 221
  (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 32 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 221 (accept_3_2 28 32 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 221 (accept_3_2 25 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 32 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 221 (accept_3_2 22 32 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 221
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 221 (accept_3_2 19 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 221 (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 221 (Polychromatic418967fa.accept_23_17_9_14_1_8205 17 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 221 (accept_3_2 16 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 221 (accept_3_2 13 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 221 (Polychromatic418967fa.accept_24_12_8_5_1_13088 12 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 221 (accept_3_2 10 32 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 221 (accept_3_2 7 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  221 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 32 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 221 (accept_3_2 4 32 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 32 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 221 (accept_3_2 1 32
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 221)))))))))))))))))))))))))))))))) (allB_succ 31 221
  (allA_of_3_0 31 31 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 221 (allA_succ_of_accept 29 30 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 221 (accept_3_2 28 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 221 (accept_3_2 25 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 30 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 221 (accept_3_2 22 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 221 (Polychromatic418967fa.accept_22_21_8_1_1_13087 21 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 221 (accept_3_2 19 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 221 (Polychromatic418967fa.accept_19_18_11_12_1_6163 18 30 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 221 (accept_3_2 16 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 221 (Polychromatic418967fa.accept_20_14_10_1_1_13086 14 30 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 221 (accept_3_2 13 30 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 221 (accept_3_2 10 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 221 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 221 (accept_3_2 7 30 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 221 (accept_3_2 4 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 221 (accept_3_2 1 30 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 221)))))))))))))))))))))))))))))) (allB_succ 29 221 (allA_succ_of_accept 28 29 221
  (accept_3_2 28 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 221
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 221 (accept_3_2 25 29 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 221
  (Polychromatic418967fa.accept_26_23_3_13_1_13085 23 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 29 221 (accept_3_2 22 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 29 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 221 (Polychromatic418967fa.accept_21_20_8_11_1_5407 20 29
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 221 (accept_3_2 19 29 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 221 (Polychromatic418967fa.accept_10_8_9_1_1_189
  18 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 221 (accept_3_2 16 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 14 29 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 221 (accept_3_2 13 29 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 221
  (Polychromatic418967fa.accept_19_11_10_12_1_2256 11 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 221 (accept_3_2 10 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 221 (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 29 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 221 (accept_3_2 7 29 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 221 (accept_3_2 4 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 29 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 221 (accept_3_2 1 29 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 221))))))))))))))))))))))))))))) (allB_succ 28 221 (allA_of_3_0 28 28 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 221 (allA_succ_of_accept 26 27 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 221 (accept_3_2 25 27 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 221 (accept_3_2 22 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 221 (accept_3_2 19 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 221 (accept_3_2 16 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 221 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 221 (accept_3_2 13 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 221
  (Polychromatic418967fa.accept_19_11_8_12_1_6204 11 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 221 (accept_3_2 10 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 221 (accept_3_2 7 27 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 221 (accept_3_2 4 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 221 (accept_3_2 1 27 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 221))))))))))))))))))))))))))) (allB_succ 26 221 (allA_succ_of_accept 25 26 221 (accept_3_2
  25 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 221 (accept_3_2 22 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 221 (accept_3_2 19 26
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 221
  (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 221 (accept_3_2 16 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 221
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 13 26 221 13 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 26 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 221 (accept_3_2 10 26
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 221 (Polychromatic418967fa.accept_6_3_2_5_1_32
  9 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 221 (accept_3_2 7 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 221 (accept_3_2 4 26 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  26 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 221 (accept_3_2 1 26 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 221)))))))))))))))))))))))))) (allB_succ 25 221 (allA_of_3_0 25
  25 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 221 (allA_succ_of_accept 23 24 221
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 221 (accept_3_2 22 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 221 (accept_3_2 19 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 221 (Polychromatic418967fa.accept_21_18_3_11_1_7049 18 24 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 221 (accept_3_2 16 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 221 (accept_3_2 13 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 24 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 221 (accept_3_2 10 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 221 (Polychromatic418967fa.accept_19_9_5_12_1_7728 9 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 221 (accept_3_2 7 24 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 221 (accept_3_2 4 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 24 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 221 (accept_3_2 1 24 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 221)))))))))))))))))))))))) (allB_succ 23 221 (allA_succ_of_accept 22 23 221 (accept_3_2 22
  23 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 221
  (Polychromatic418967fa.accept_19_2_4_12_1_13084 21 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 221 (accept_3_2 19 23 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 221
  (Polychromatic418967fa.accept_21_17_2_11_1_8656 17 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 221 (accept_3_2 16 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 221 (Polychromatic418967fa.accept_24_15_23_5_1_13083 15 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 221 (accept_3_2 13 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 221
  (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 221 (accept_3_2 10 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 221 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 221 (accept_3_2 7 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 221 (accept_3_2 4 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 3 23 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 221 (accept_3_2 1 23 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 221))))))))))))))))))))))) (allB_succ 22 221 (allA_of_3_0 22 22 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 21 221 (allA_succ_of_accept 20 21 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 221 (accept_3_2 19 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 221 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 221 (accept_3_2 16 21 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 221 (accept_3_2 13 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 221 (Polychromatic418967fa.accept_23_12_21_14_1_13082 12 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 221 (accept_3_2 10 21 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 221 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 221 (accept_3_2 7 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 221 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 21 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 221 (accept_3_2 4 21 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 221 (accept_3_2 1 21 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 221))))))))))))))))))))) (allB_succ 20 221 (allA_succ_of_accept
  19 20 221 (accept_3_2 19 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 221
  (Polychromatic418967fa.accept_19_18_1_12_1_6235 18 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 221 (accept_3_2 16 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 221 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 221 (accept_3_2 13
  20 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 221 (accept_3_2 10 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 221 (accept_3_2 7 20 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 221 (accept_3_2 4 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 221 (accept_3_2 1 20 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 221)))))))))))))))))))) (allB_succ 19 221 (allA_of_3_0 19 19 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 221 (allA_succ_of_accept 17 18 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 18 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 221 (accept_3_2 16 18 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 221 (accept_3_2 13 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 221 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 221 (accept_3_2 10 18 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 221 (accept_3_2 7 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  221 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 221 (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 18 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 221 (accept_3_2 4 18 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 221 (Polychromatic418967fa.accept_22_2_18_1_1_13081
  2 18 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 221 (accept_3_2 1 18
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 221)))))))))))))))))) (allB_succ 17 221 (allA_succ_of_accept
  16 17 221 (accept_3_2 16 17 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 17 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 221 (accept_3_2 13 17 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 221 (accept_3_2 10 17
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 221
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 17 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 221 (accept_3_2 7 17 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 5
  17 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 221 (accept_3_2 4 17 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 17 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 221 (accept_3_2 1 17 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  221))))))))))))))))) (allB_succ 16 221 (allA_of_3_0 16 16 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  221 (allA_succ_of_accept 14 15 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 221 (accept_3_2 13 15 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  15 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 221 (accept_3_2 10 15
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 221 (accept_3_2 7 15 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  15 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 221 (accept_3_2 4 15 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  15 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 221 (accept_3_2 1 15 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  221))))))))))))))) (allB_succ 14 221 (allA_succ_of_accept 13 14 221 (accept_3_2 13 14 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 12 14 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 221 (accept_3_2 10 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 14 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 221 (accept_3_2 7 14 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 221 (Polychromatic418967fa.accept_19_6_14_12_1_4811 6 14 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 221 (accept_3_2 4 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 14 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 221 (accept_3_2 1 14 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 221)))))))))))))) (allB_succ 13 221 (allA_of_3_0 13 13 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 221 (allA_succ_of_accept 11 12 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 221 (accept_3_2 10 12 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  12 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 221 (accept_3_2 7 12 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 221 (Polychromatic418967fa.accept_21_5_12_11_1_5429 5 12 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 221 (accept_3_2 4 12 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  12 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 221 (accept_3_2 1 12 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 221)))))))))))) (allB_succ 11 221 (allA_succ_of_accept 10 11 221
  (accept_3_2 10 11 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 221
  (Polychromatic418967fa.accept_25_9_11_21_1_13080 9 11 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 221 (accept_3_2 7 11 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 221
  (Polychromatic418967fa.accept_19_5_11_12_1_11765 5 11 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 221 (accept_3_2 4 11 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 11 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 221 (accept_3_2 1 11 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 221))))))))))) (allB_succ 10 221 (allA_of_3_0 10 10 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 9 221 (allA_succ_of_accept 8 9 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 221 (accept_3_2 7 9 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 221 (accept_3_2 4 9 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 221
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 9 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 221 (accept_3_2 1 9 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 9 221))))))))) (allB_succ 8 221 (allA_succ_of_accept 7 8 221 (accept_3_2 7 8 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 8 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 221 (accept_3_2 4 8 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 221 (accept_3_2 1 8 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 221)))))))) (allB_succ 7 221 (allA_of_3_0 7 7 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 221 (allA_succ_of_accept 5 6 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 221 (accept_3_2 4 6 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 6 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 221 (accept_3_2 1 6 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 221)))))) (allB_succ 5 221 (allA_succ_of_accept 4 5 221
  (accept_3_2 4 5 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 221
  (Polychromatic418967fa.accept_20_3_5_1_1_4391 3 5 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 221 (accept_3_2 1 5 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 221))))) (allB_succ 4 221 (allA_of_3_0 4 4 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 221 (allA_succ_of_accept 2 3 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 221 (accept_3_2 1 3 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 221))) (allB_succ 2 221 (allA_succ_of_accept 1 2 221 (accept_3_2 1 2 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 221)) (allB_two
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


