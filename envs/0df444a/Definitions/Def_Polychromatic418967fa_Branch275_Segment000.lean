-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch275_Segment000
-- name    : Polychromatic418967fa_Branch275_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:50:27.113991+00:00
-- url     : https://prove2.me/theorems/4cdd17bf-ac97-4c84-b034-793dd2cd5e24
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

def Polychromatic418967fa.branch_275_segment_000 : allB 123 275 :=
  allB_succ 122 275 (allA_succ_of_accept 121 122 275 (accept_3_2 121 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 120 122 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 119
  122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 275 (accept_3_2 118
  122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 116 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 275 (accept_3_2 115 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 122 275 (Polychromatic418967fa.accept_13_10_5_2_1_1477 114 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 275 (accept_3_2 112 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 110 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 275 (accept_3_2 109 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 108 122
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 275
  (Polychromatic418967fa.accept_10_7_2_5_1_298 107 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 275 (accept_3_2 106 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 275 (accept_3_2 103 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 275 (Polychromatic418967fa.accept_15_12_2_5_1_3939 102
  122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 275 (accept_3_2 100 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 98 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 275 (accept_3_2 97 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 275
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 95 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 275 (accept_3_2 94 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 275 (accept_3_2 91 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 275 (accept_3_2 88 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 86 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 275 (accept_3_2 85 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 275 (Polychromatic418967fa.accept_20_4_2_15_1_6904 84 122
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 275 (accept_3_2 82 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 275 (accept_3_2 79 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 275 (accept_3_2 76 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 74 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 275 (accept_3_2 73 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 122
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 275 (accept_3_2 70 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 275 (accept_3_2 67 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 275 (Polychromatic418967fa.accept_21_3_17_2_1_11043 66 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 275 (accept_3_2 64 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 275 (accept_3_2 61 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 275 (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 275
  (Polychromatic418967fa.accept_13_7_5_2_1_401 59 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 275 (accept_3_2 58 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 275 (accept_3_2 55 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 275 (accept_3_2 52 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 275 (accept_3_2 49 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 275 (accept_3_2 46 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 275 (accept_3_2 43 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 275 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 122
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 275 (accept_3_2 40 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 275 (accept_3_2 37 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 275
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 275 (accept_3_2 34 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 275 (accept_3_2 31 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 275 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 122
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 275 (accept_3_2 28 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 275 (accept_3_2 25 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 275 (Polychromatic418967fa.accept_20_4_2_15_1_6904 24 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 275 (accept_3_2 22 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 275 (accept_3_2 19 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 275 (accept_3_2 16 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 275 (accept_3_2 13 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 275 (accept_3_2 10 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 275 (accept_3_2 7 122 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 275 (accept_3_2 4 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 275 (Polychromatic418967fa.accept_27_2_14_5_1_16920 2 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 275 (accept_3_2 1 122 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 122
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 275 (allA_of_3_0 121 121 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 275
  (allA_succ_of_accept 119 120 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 119 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 275 (accept_3_2 118 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 120 275 (Polychromatic418967fa.accept_16_5_8_3_1_4240 117 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 116 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 115 120 275 5 23 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 114 120 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 114 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 275
  (Polychromatic418967fa.accept_13_9_3_2_1_399 113 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 120 275 (accept_3_2 112 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 120 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 120 275 5 22 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 120 275 (accept_3_2 109 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 107 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 275 (accept_3_2 106 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 120 275 5 21 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 120 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 104 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 275 (accept_3_2 103 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 102 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 275 5 20 24 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 275
  (Polychromatic418967fa.accept_14_1_8_9_1_1312 99 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 275 (accept_3_2 97 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 120 275 5 19 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 120 275 (accept_3_2 94 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 275 (Polychromatic418967fa.accept_16_13_8_3_1_5374 93 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 275 (accept_3_2 91 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  120 275 5 18 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 120 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 275 (accept_3_2 88 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 275
  (Polychromatic418967fa.accept_19_10_6_9_1_7312 86 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 120 275 5 17 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 120 275 (Polychromatic418967fa.accept_16_4_8_3_1_4206 84 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 120 275 (accept_3_2 82 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 120 275 (Polychromatic418967fa.accept_18_9_12_5_1_864 81 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 120 275 5 16 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 275 (accept_3_2 79 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 120 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 275 (accept_3_2 76 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 120 275 5 15 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 120 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 275 (accept_3_2 73 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 275 (Polychromatic418967fa.accept_19_15_6_9_1_3334 72 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 275 5 14 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 120 275 (Polychromatic418967fa.accept_16_4_8_3_1_4206 68 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 275 (accept_3_2 67 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 120 275 5 13 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 120 275 (accept_3_2 64 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 275 (accept_3_2 61 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  120 275 5 12 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 275 (accept_3_2 58 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 120 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 120 275 5 11 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 120 275 (Polychromatic418967fa.accept_19_16_6_9_1_7335 54 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 120 275 (accept_3_2 52 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 120 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 120 275 5 10 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 120 275 (accept_3_2 49 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 120 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 275 (accept_3_2 46 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 275 5 9 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 275 (accept_3_2 43 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 275 5 8 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 275
  (Polychromatic418967fa.accept_21_18_15_2_1_4806 39 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 275 (accept_3_2 37 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 120 275 5 7 24 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 275 (accept_3_2 34
  120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 275
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 275 (Polychromatic418967fa.accept_17_15_1_3_1_1488 32 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 275 (accept_3_2 31 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 120 275 5 6 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 120 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 275 (accept_3_2 28 120 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 120 275 5 5 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 275 (accept_3_2 22 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 275
  (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 275 5 4 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 275 (accept_3_2 19 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 275 (accept_3_2 16 120 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 275 5 3 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 275 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 275 (accept_3_2 13 120
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 275
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 275 5 2 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 9
  120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 275 (accept_3_2 7 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 120 275 5 1 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 120 275 (accept_3_2 4 120 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 120 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 275 (accept_3_2 1 120 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 275 (allA_succ_of_accept 118 119 275 (accept_3_2 118 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 117 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144
  116 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 275 (accept_3_2
  115 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 114 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 113 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 275 (accept_3_2 112 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 111 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 275
  (Polychromatic418967fa.accept_14_12_7_9_1_726 110 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 275 (accept_3_2 109 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 275 (accept_3_2 106 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 105 119
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 275
  (Polychromatic418967fa.accept_10_4_9_5_1_84 104 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 275 (accept_3_2 103 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 101 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 275 (accept_3_2 100 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 275 (Polychromatic418967fa.accept_15_9_14_5_1_2086 99 119
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 98 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 275 (accept_3_2 97 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 275 (Polychromatic418967fa.accept_16_15_7_3_1_4273 95 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 275 (accept_3_2 94 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 119 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 275
  (Polychromatic418967fa.accept_8_4_7_3_1_144 92 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 275 (accept_3_2 91 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 275 (Polychromatic418967fa.accept_16_10_7_3_1_6601 90 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 275 (accept_3_2 88 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 275
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 86 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 275 (accept_3_2 85 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 83 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 275 (accept_3_2 82 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 119 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 275 (accept_3_2 79 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 275 (accept_3_2 76 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 119 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 275
  (Polychromatic418967fa.accept_10_4_9_5_1_84 74 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 275 (accept_3_2 73 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 275 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 275 (accept_3_2 70 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 275
  (Polychromatic418967fa.accept_8_4_7_3_1_144 68 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 275 (accept_3_2 67 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 275 (Polychromatic418967fa.accept_20_5_19_15_1_3946 65 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 275 (accept_3_2 64 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 275 (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 119
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 275 (accept_3_2 61 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 275 (Polychromatic418967fa.accept_16_11_7_3_1_3163 59 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 275 (accept_3_2 58 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 119 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 275
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 275 (accept_3_2 55 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 275 (accept_3_2 52 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 275
  (Polychromatic418967fa.accept_18_14_11_5_1_7967 50 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 119 275 (accept_3_2 49 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 119
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 275 (accept_3_2 46 119
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 275
  (Polychromatic418967fa.accept_19_7_5_9_1_10202 45 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 275 (accept_3_2 43 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 275 (Polychromatic418967fa.accept_10_1_9_5_1_83
  41 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 275 (accept_3_2 40
  119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 119 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 38 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 275 (accept_3_2 37 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237
  35 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 275 (accept_3_2 34
  119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 119 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 275 (accept_3_2 31 119 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 275
  (Polychromatic418967fa.accept_21_8_14_2_1_7981 29 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 275 (accept_3_2 28 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 275 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 275 (accept_3_2 25 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 275 (accept_3_2 22 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 275 (accept_3_2 19 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 275 (Polychromatic418967fa.accept_19_18_5_9_1_1112 18 119 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 275 (accept_3_2 16 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 275 (accept_3_2 13 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 275 (accept_3_2 10 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 275 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 275 (accept_3_2 7 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 275
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 275 (accept_3_2 4 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 275 (Polychromatic418967fa.accept_14_2_7_9_1_2937 2 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 275 (accept_3_2 1 119 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 275 (allA_of_3_0 118 118 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 275
  (allA_succ_of_accept 116 117 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 275 (accept_3_2 115 117 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 113 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 275 (accept_3_2 112 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 275 (accept_3_2 109 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 275
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 107 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 117 275 (accept_3_2 106 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 117 275 (Polychromatic418967fa.accept_14_7_5_9_1_2911 105 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 275 (Polychromatic418967fa.accept_6_2_3_5_1_26
  104 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 275 (accept_3_2
  103 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 117 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 275 (accept_3_2 100 117 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 117 275 (accept_3_2 97 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 117 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 96 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 275 (accept_3_2 94 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 275 (accept_3_2 91 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 275 (Polychromatic418967fa.accept_19_13_3_9_1_5980 89 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 275 (accept_3_2 88 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 275 (accept_3_2 85 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 83 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 275 (accept_3_2 82 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 275 (accept_3_2 79 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 275 (Polychromatic418967fa.accept_14_7_5_9_1_2911 77 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 275 (accept_3_2 76 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 275 (accept_3_2 73 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 275 (Polychromatic418967fa.accept_19_14_3_9_1_2157 71 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 275 (accept_3_2 70 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 275 (accept_3_2 67 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 275 (Polychromatic418967fa.accept_17_14_15_3_1_4618 65 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 275 (accept_3_2 64 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 275 (accept_3_2 61 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 275 (accept_3_2 58 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 275 (Polychromatic418967fa.accept_23_11_2_22_1_7053 57 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 275 (accept_3_2 55 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 275 (accept_3_2 52 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 275 (accept_3_2 49 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 275 (accept_3_2 46 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 275 (accept_3_2 43 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 275 (Polychromatic418967fa.accept_27_14_9_5_1_9255 41 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 275 (accept_3_2 40 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 275 (accept_3_2 37 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 275 (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 275 (accept_3_2 34 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 275 (accept_3_2 31 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 275 (Polychromatic418967fa.accept_17_12_15_3_1_7168 29 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 275 (accept_3_2 28 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 275 (accept_3_2 25 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 275 (accept_3_2 22 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 275 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 117
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 275 (accept_3_2 19 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 275 (accept_3_2 16 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 275 (accept_3_2 13 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 275 (accept_3_2 10 117 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 275 (accept_3_2 7 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 275 (Polychromatic418967fa.accept_20_5_17_15_1_6858 5 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 275 (accept_3_2 4 117 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 275 (accept_3_2 1 117 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 275 (allA_succ_of_accept 115 116 275 (accept_3_2 115 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 114 116 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 113 116
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 275 (accept_3_2 112 116
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 110 116 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 275 (accept_3_2 109 116 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 108 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 275
  (Polychromatic418967fa.accept_13_3_12_2_1_385 107 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 275 (accept_3_2 106 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 104 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 275 (accept_3_2 103 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 116
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 275 (accept_3_2 100 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 275 (accept_3_2 97 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 95 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 275 (accept_3_2 94 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 275 (accept_3_2 91 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 275 (accept_3_2 88 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 275 (accept_3_2 85 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 275 (accept_3_2 82 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 275 (Polychromatic418967fa.accept_19_4_2_9_1_4584 80 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 275 (accept_3_2 79 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 275
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 275 (accept_3_2 76 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 275 (accept_3_2 73 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 275 (accept_3_2 70 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 275 (accept_3_2 67 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 275 (accept_3_2 64 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 275 (accept_3_2 61 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 275
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 275 (accept_3_2 58 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 275 (accept_3_2 55 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 275
  (Polychromatic418967fa.accept_13_1_12_2_1_384 53 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 275 (accept_3_2 52 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 275 (accept_3_2 49 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 275 (accept_3_2 46 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 275 (accept_3_2 43 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 275 (accept_3_2 40 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 275 (accept_3_2 37 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 275
  (Polychromatic418967fa.accept_18_17_8_5_1_2769 35 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 275 (accept_3_2 34 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 275 (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 275 (accept_3_2 31 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 275 (accept_3_2 28 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 275 (accept_3_2 25 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 275 (accept_3_2 22 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 275 (accept_3_2 19 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 116 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 275
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 275 (accept_3_2 16 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 275 (accept_3_2 13 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 275 (accept_3_2 10 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 275 (accept_3_2 7 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 275 (accept_3_2 4 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 275 (accept_3_2 1 116 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 275 (allA_of_3_0 115 115 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 275
  (allA_succ_of_accept 113 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 275 (accept_3_2 112 114 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 111 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 110 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 275 (accept_3_2 109 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 108 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 107 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 275 (accept_3_2 106 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 104 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 114 275 (accept_3_2 103 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 114 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 275 (accept_3_2 100 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 275 (Polychromatic418967fa.accept_10_9_4_5_1_616
  99 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 98 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 275 (accept_3_2 97 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 114 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 96 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 114 275 (Polychromatic418967fa.accept_14_11_2_9_1_5873 95 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 275 (accept_3_2 94 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 92 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 275 (accept_3_2 91 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 275 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 275 (accept_3_2 88 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 87 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 86 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 275 (accept_3_2 85 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 275 (accept_3_2 82 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 275 (accept_3_2 79 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 114 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 78 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 275 (accept_3_2 76 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 275 (accept_3_2 73 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 114 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 275 (accept_3_2 70 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 275
  (Polychromatic418967fa.accept_13_3_10_2_1_381 68 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 275 (accept_3_2 67 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 275 (accept_3_2 64 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 275 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 275 (accept_3_2 61 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 275 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 59 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 275 (accept_3_2 58 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 275 (accept_3_2 55 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 275 (Polychromatic418967fa.accept_16_6_2_3_1_4223 54 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 275 (accept_3_2 52 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 275
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 114 275 (accept_3_2 49 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 114 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 275 (accept_3_2 46 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 275 (accept_3_2 43 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 275 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 275 (accept_3_2 40 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 275 (accept_3_2 37 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 275 (accept_3_2 34 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 275
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 275 (accept_3_2 31 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 275 (accept_3_2 28 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 275 (accept_3_2 25 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 275 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 275 (Polychromatic418967fa.accept_22_1_4_11_1_13806 23 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 275 (accept_3_2 22 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 275 (accept_3_2 19 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 275 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 275 (accept_3_2 16 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 275 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 114 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 275 (accept_3_2 13 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 275 (accept_3_2 10 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 275 (accept_3_2 7 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 275 (accept_3_2 4 114 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 275 (accept_3_2 1 114 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 275 (allA_succ_of_accept 112 113 275 (accept_3_2 112 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 113 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 275 (accept_3_2 109 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 108 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 107 113 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 275 (accept_3_2 106 113 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 105 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 104 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 275 (accept_3_2 103 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 275 (accept_3_2 100 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 275 (Polychromatic418967fa.accept_17_14_11_3_1_4653 99 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 275 (accept_3_2 97 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 96 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 275 (Polychromatic418967fa.accept_17_10_11_3_1_3442 95 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 275 (accept_3_2 94 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 275 (Polychromatic418967fa.accept_15_3_8_5_1_2105 93 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 275
  (Polychromatic418967fa.accept_10_2_3_5_1_996 92 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 275 (accept_3_2 91 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 89 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 275 (accept_3_2 88 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 275 (accept_3_2 85 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 84 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 275 (accept_3_2 82 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 81 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 275 (accept_3_2 79 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 275 (accept_3_2 76 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 275 (Polychromatic418967fa.accept_22_9_3_11_1_15411 75 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 275 (accept_3_2 73 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 275 (accept_3_2 70 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 275
  (Polychromatic418967fa.accept_10_8_3_5_1_613 68 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 275 (accept_3_2 67 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 275 (Polychromatic418967fa.accept_17_14_11_3_1_4653 65 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 275 (accept_3_2 64 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 275 (accept_3_2 61 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 275 (Polychromatic418967fa.accept_17_9_11_3_1_2353 60 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 275 (accept_3_2 58 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 275 (accept_3_2 55 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 275 (accept_3_2 52 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 275 (Polychromatic418967fa.accept_19_13_18_9_1_10237 51
  113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 275 (accept_3_2 49 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 275 (accept_3_2 46 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 275 (accept_3_2 43 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 275 (accept_3_2 40 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 275 (Polychromatic418967fa.accept_23_16_21_22_1_11998 39 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 275 (accept_3_2 37 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 275 (Polychromatic418967fa.accept_19_16_18_9_1_3295 35 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 275 (accept_3_2 34 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 275 (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 275
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 275 (accept_3_2 31 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 275 (accept_3_2 28 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 275 (accept_3_2 25 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 275 (Polychromatic418967fa.accept_22_1_3_11_1_10754 23 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 275 (accept_3_2 22 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 275 (Polychromatic418967fa.accept_19_2_18_9_1_8829 21 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 275 (accept_3_2 19 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 275 (accept_3_2 16 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 275 (Polychromatic418967fa.accept_19_15_18_9_1_8869 15 113 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 275 (accept_3_2 13 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 275 (accept_3_2 10 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 275 (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 113
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 275
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 275 (accept_3_2 7 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 275 (accept_3_2 4 113 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 275 (accept_3_2 1 113 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 275 (allA_of_3_0 112 112 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 275
  (allA_succ_of_accept 110 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 275 (accept_3_2 109 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 107 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 275 (accept_3_2 106 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 275 (accept_3_2 103 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 111
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 275 (accept_3_2 100 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 275 (accept_3_2 97 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 275 (accept_3_2 94 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 275 (accept_3_2 91 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 275 (Polychromatic418967fa.accept_19_14_16_9_1_8834 90 111 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 275 (accept_3_2 88 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 275 (accept_3_2 85 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 275 (accept_3_2 82 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 275 (accept_3_2 79 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 275
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 77 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 111 275 (accept_3_2 76 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 111 275 (Polychromatic418967fa.accept_16_11_15_3_1_1304 75 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 74
  111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 275 (accept_3_2 73
  111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 275
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 275 (accept_3_2 70 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 275 (accept_3_2 67
  111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 275 (accept_3_2 64 111 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 275 (accept_3_2 61 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 275 (accept_3_2 58 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 275 (accept_3_2 55 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 275 (accept_3_2 52 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 275 (accept_3_2 49 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 275 (accept_3_2 46 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 275 (accept_3_2 43 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 275 (accept_3_2 40 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 275 (accept_3_2 37 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 275 (accept_3_2 34 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 275 (accept_3_2 31 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 275 (Polychromatic418967fa.accept_20_10_11_15_1_6885 30 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 275 (accept_3_2 28 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 111
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 275 (accept_3_2 25 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 275 (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 275 (accept_3_2 22 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 275 (accept_3_2 19 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 275 (accept_3_2 16 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 275 (accept_3_2 13 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 275 (accept_3_2 10 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 275 (accept_3_2 7 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 275 (accept_3_2 4 111 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 275 (accept_3_2 1 111 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 275 (allA_succ_of_accept 109 110 275 (accept_3_2 109 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 110
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 275 (accept_3_2 106 110
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 110 275 5 21 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 110 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 104 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 110 275 (accept_3_2 103 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 110 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 275 5 20 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 110 275 11 9 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 110 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 98 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 110 275 (accept_3_2 97 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 110 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 110 275 5 19 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 110 275 (accept_3_2 94 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 110 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 92 110
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 275 (accept_3_2 91 110
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 110 275 5 18 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 110 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 110 275 11 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 110 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 110 275 (Polychromatic418967fa.accept_13_8_6_2_1_865
  86 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 110 275 5 17 22 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 110 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 84 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 110 275 (Polychromatic418967fa.accept_20_3_10_15_1_620 83 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 110 275 (accept_3_2 82 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 110 275 5 16 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 110 275 (accept_3_2 79 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 110 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 110 275 11 7 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 110 275 (accept_3_2 76
  110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 110 275 5 15 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 110 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 110 275 (accept_3_2 73 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 110 275 (Polychromatic418967fa.accept_20_12_10_15_1_9869 72 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 275 5 14 22 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 110 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 275 (accept_3_2 67 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 110 275 11 6 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 275 5 13 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 110 275 (accept_3_2 64 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 110 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 275 (Polychromatic418967fa.accept_9_8_2_5_1_237
  62 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 275 (accept_3_2 61
  110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 110 275 5 12 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 110 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 275 (accept_3_2 58 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 110 275 55 1 2 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 110 275
  (Polychromatic418967fa.accept_20_14_10_15_1_3952 54 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 275 (accept_3_2 52 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 275 5 10 22 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 275 (accept_3_2 49 110 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 275 (Polychromatic418967fa.accept_9_3_2_5_1_234
  48 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 275
  (Polychromatic418967fa.accept_13_8_6_2_1_865 47 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 275 (accept_3_2 46 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  110 275 5 9 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44
  110 275 11 4 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 110 275 (accept_3_2 43 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 275 5 8 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 110 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 275 (accept_3_2 37 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 110 275 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 110 275 5 7 22 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 110 275 (accept_3_2 34 110 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 110 275 11 3 10 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 110 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 275 (accept_3_2 31 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  110 275 5 6 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 110 275 (accept_3_2 28 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 110 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 110 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 110 275 5 5 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 110 275 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 275 11 2 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 275 5 4 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 275 (accept_3_2 19
  110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 275 (accept_3_2 16 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 110 275 5 3 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 110 275 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 275 (accept_3_2 13 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 110 275 11 1 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 110 275 5 2 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 275 (accept_3_2 7 110 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 275 5 1 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 275 (accept_3_2 4 110 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 275
  (Polychromatic418967fa.accept_19_2_15_9_1_7318 2 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 275 (accept_3_2 1 110 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 275 (allA_of_3_0 109 109 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 275
  (allA_succ_of_accept 107 108 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 107 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 275 (accept_3_2 106 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 275 (Polychromatic418967fa.accept_16_9_12_3_1_3138 105 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 104 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 275 (accept_3_2 103 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 102 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 108 275 (Polychromatic418967fa.accept_19_6_13_9_1_3291 101 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 275 (accept_3_2 100 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 275
  (Polychromatic418967fa.accept_15_8_3_5_1_608 98 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 275 (accept_3_2 97 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 95 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 275 (accept_3_2 94 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 93 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 92 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 275 (accept_3_2 91 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 275 (accept_3_2 88 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 275
  (Polychromatic418967fa.accept_17_1_6_3_1_4700 86 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 275 (accept_3_2 85 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 108 275 (Polychromatic418967fa.accept_13_6_4_2_1_1433 84 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 275 (accept_3_2 82 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 81 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 275
  (Polychromatic418967fa.accept_19_4_13_9_1_5968 80 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 275 (accept_3_2 79 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 275 (accept_3_2 76 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 275
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 74 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 108 275 (accept_3_2 73 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 108 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 108 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 275 (accept_3_2 70 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461
  69 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 275 (accept_3_2 67 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 66 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 275 (Polychromatic418967fa.accept_17_14_6_3_1_2362 65 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 275 (accept_3_2 64 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 275 (accept_3_2 61 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 275 (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 275 (Polychromatic418967fa.accept_21_17_3_2_1_2111 59 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 275 (accept_3_2 58 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 275
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 56 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 275 (accept_3_2 55 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 53 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 275 (accept_3_2 52 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 275 (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 108
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 275 (accept_3_2 49 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 275 (accept_3_2 46 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 275 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 275
  (Polychromatic418967fa.accept_13_5_4_2_1_846 44 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 275 (accept_3_2 43 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 275 (accept_3_2 40 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 275
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 275 (accept_3_2 37 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 108 275 (Polychromatic418967fa.accept_17_1_6_3_1_4700 35 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 275 (accept_3_2 34 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 275 (accept_3_2 31 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 275 (Polychromatic418967fa.accept_20_10_8_15_1_11332 30 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 275 (accept_3_2 28 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 275 (accept_3_2 25 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 275 (accept_3_2 22 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 275 (accept_3_2 19 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 275 (accept_3_2 16 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 275
  (Polychromatic418967fa.accept_17_14_6_3_1_2362 14 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 275 (accept_3_2 13 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 275 (accept_3_2 10 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 108 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 275 (accept_3_2 7 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 275 (accept_3_2 4 108 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 275 (accept_3_2 1 108 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 275 (allA_succ_of_accept 106 107 275 (accept_3_2 106 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 105 107 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 104
  107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 275 (accept_3_2 103
  107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 275
  (Polychromatic418967fa.accept_9_3_8_5_1_65 102 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 107 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 275 (accept_3_2 100 107 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 275 (Polychromatic418967fa.accept_23_7_15_22_1_15360 99 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 275
  (Polychromatic418967fa.accept_10_8_7_5_1_602 98 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 275 (accept_3_2 97 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 275 (Polychromatic418967fa.accept_16_15_11_3_1_2179 95 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 275 (accept_3_2 94 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 93 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 275 (accept_3_2 91 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 90 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 89 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 275 (accept_3_2 88 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 86 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 275 (accept_3_2 85 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 275 (accept_3_2 82 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 275 (Polychromatic418967fa.accept_19_5_12_9_1_4588 81 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 275
  (Polychromatic418967fa.accept_18_8_17_5_1_9273 80 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 275 (accept_3_2 79 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 275 (accept_3_2 76 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 275 (accept_3_2 73 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 275 (accept_3_2 70 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 275
  (Polychromatic418967fa.accept_10_8_7_5_1_602 68 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 275 (accept_3_2 67 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 275 (accept_3_2 64 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 275
  (Polychromatic418967fa.accept_10_2_7_5_1_605 62 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 275 (accept_3_2 61 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 275 (accept_3_2 58 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 275 (accept_3_2 55 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 275 (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 275 (accept_3_2 52 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 275
  (Polychromatic418967fa.accept_13_11_3_2_1_863 50 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 275 (accept_3_2 49 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 275 (accept_3_2 46 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 275 (Polychromatic418967fa.accept_20_5_7_15_1_2668 45 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 275
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 275 (accept_3_2 43 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 275 (accept_3_2 40 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 275 (accept_3_2 37 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 275 (accept_3_2 34 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 275
  (Polychromatic418967fa.accept_10_2_7_5_1_605 32 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 275 (accept_3_2 31 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 275 (accept_3_2 28 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 275 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 275 (accept_3_2 25 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 275 (accept_3_2 22 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 275 (accept_3_2 19 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 275 (Polychromatic418967fa.accept_26_17_3_15_1_16919 17 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 275 (accept_3_2 16 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 107 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 275
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 275 (accept_3_2 13 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 275 (accept_3_2 10 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 275
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 275 (accept_3_2 7 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 275 (accept_3_2 4 107 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 107 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 275 (accept_3_2 1 107 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 275 (allA_of_3_0 106 106 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 275
  (allA_succ_of_accept 104 105 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 275 (accept_3_2 103 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 105 275 5 20 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 105 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 105 275 (accept_3_2 97 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 105 275 (Polychromatic418967fa.accept_14_12_7_9_1_726 96 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 105 275 5 19 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 105 275 (accept_3_2 94 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 275 (accept_3_2 91 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 275 5 18 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 275 (accept_3_2 88 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 275 5 17 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 105 275
  (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 275 (accept_3_2 82 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 275 (Polychromatic418967fa.accept_13_3_1_2_1_2960 81 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 105 275 5 16 21 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 275 (accept_3_2 79 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 275
  (Polychromatic418967fa.accept_13_12_1_2_1_845 77 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 275 (accept_3_2 76 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  105 275 5 15 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 275 (accept_3_2 73 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 105 275 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 105 275 5 14 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 105 275 (Polychromatic418967fa.accept_19_12_10_9_1_3326 69 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 275 (accept_3_2 67 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 105 275 5 13 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 105 275 (accept_3_2 64 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 275 (accept_3_2 61 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 275 5 12 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 275
  (Polychromatic418967fa.accept_20_19_5_15_1_5380 59 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 105 275 (accept_3_2 58 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 275 5 11 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 275 (accept_3_2 52 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 275 5 10 21 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 275 (accept_3_2 49 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48
  105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 275 (accept_3_2 46 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  105 275 5 9 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 105 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 275 (accept_3_2 43 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 275 (Polychromatic418967fa.accept_19_3_10_9_1_7338 41 105
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 275 5 8 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 275
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 275 (accept_3_2 37 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 275 (Polychromatic418967fa.accept_20_16_5_15_1_5364 36 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 275 5 7 21 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 275 (accept_3_2 34 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828
  33 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 275 (accept_3_2 31 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  105 275 5 6 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 105 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 105 275 (accept_3_2 28 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 275 5 5 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 275
  (Polychromatic418967fa.accept_18_6_15_5_1_6563 24 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 275 (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 275 (accept_3_2 22 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 275 5 4 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 275 (accept_3_2 19 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 275 (accept_3_2 16 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  105 275 5 3 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 275 (accept_3_2 13 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 275 5 2 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 275
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 275 (accept_3_2 7 105 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 275 5 1 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 275 (accept_3_2 4 105 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 275 (accept_3_2 1 105 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 275 (allA_succ_of_accept 103 104 275 (accept_3_2 103 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 104 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 275 (accept_3_2 100 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 104 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 275 (accept_3_2 97 104 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 96 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 275 (accept_3_2 94 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 275 (accept_3_2 91 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 275 (Polychromatic418967fa.accept_17_5_2_3_1_9775 90 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 275
  (Polychromatic418967fa.accept_10_9_4_5_1_616 89 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 275 (accept_3_2 88 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 86 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 275 (accept_3_2 85 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 275 (Polychromatic418967fa.accept_15_9_14_5_1_2086 84 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 83 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 275 (accept_3_2 82 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 275 (accept_3_2 79 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 275 (accept_3_2 76 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 275 (accept_3_2 73 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 275 (Polychromatic418967fa.accept_21_9_20_2_1_8000 72 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 275 (accept_3_2 70 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 68 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 275 (accept_3_2 67 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 275
  (Polychromatic418967fa.accept_17_14_2_3_1_7172 65 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 275 (accept_3_2 64 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 275 (accept_3_2 61 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 275 (accept_3_2 58 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 275 (accept_3_2 55 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 275 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 275 (accept_3_2 52 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 275 (accept_3_2 49 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 275 (Polychromatic418967fa.accept_17_14_2_3_1_7172 48 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 275 (accept_3_2 46 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 275 (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 275 (accept_3_2 43 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 275 (Polychromatic418967fa.accept_20_2_4_15_1_6911 42 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 275
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 275 (accept_3_2 40 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 275 (accept_3_2 37 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 275
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 275 (accept_3_2 34 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 275 (accept_3_2 31 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 275 (Polychromatic418967fa.accept_20_10_4_15_1_12657 30 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 275 (accept_3_2 28 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 275 (accept_3_2 25 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 275 (accept_3_2 22 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 275 (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 275 (accept_3_2 19 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 275 (accept_3_2 16 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 275 (accept_3_2 13 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 275 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 104
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 275 (accept_3_2 10 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 275 (accept_3_2 7 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 104 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 275
  (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 275 (accept_3_2 4 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 275 (accept_3_2 1 104 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 275 (allA_of_3_0 103 103 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 275 (allA_succ_of_accept 101
  102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 275 (accept_3_2 100 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 99 102 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 275 (accept_3_2 97 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235
  96 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 275
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 95 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 275 (accept_3_2 94 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 275 (accept_3_2 91 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 275 (accept_3_2 88 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 86 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 275 (accept_3_2 85 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 102
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 275 (accept_3_2 82 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 102 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 275 (accept_3_2 79 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 275 (accept_3_2 76 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 102 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 275 (accept_3_2 73 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 275 (accept_3_2 70 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 275 (accept_3_2 67 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 275 (accept_3_2 64 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 102 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 275 (accept_3_2 61 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 275
  (Polychromatic418967fa.accept_16_11_6_3_1_6564 59 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 275 (accept_3_2 58 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 102 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 275 (accept_3_2 55 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 275 (accept_3_2 52 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 102 275 (Polychromatic418967fa.accept_16_2_6_3_1_5396 50 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 275 (accept_3_2 49 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 275 (accept_3_2 46 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 275 (accept_3_2 43 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 275 (accept_3_2 40 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 275 (accept_3_2 37 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 275 (accept_3_2 34 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 275 (accept_3_2 31 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 275 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 102
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 275 (accept_3_2 28 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 275 (accept_3_2 25 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 275 (accept_3_2 22 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 275 (accept_3_2 19 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 275 (accept_3_2 16 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 275 (Polychromatic418967fa.accept_27_14_21_5_1_16918 14 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 275 (accept_3_2 13 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 275 (accept_3_2 10 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 275 (accept_3_2 7 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 275 (accept_3_2 4 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 102 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 275 (accept_3_2 1 102 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 275 (allA_succ_of_accept 100 101 275 (accept_3_2 100 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 101 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 275 (accept_3_2 97 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 275 (Polychromatic418967fa.accept_7_5_3_2_1_249
  96 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 275
  (Polychromatic418967fa.accept_21_11_17_2_1_4749 95 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 101 275 (accept_3_2 94 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 101 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 101 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 275 (accept_3_2 91 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 90
  101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 275 (accept_3_2 88 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 275 (accept_3_2 85 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 275 (accept_3_2 82 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 275 (Polychromatic418967fa.accept_13_3_10_2_1_381 81 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 275 (accept_3_2 79 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 275
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 275 (accept_3_2 76 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 101 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 275 (accept_3_2 73 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 275 (Polychromatic418967fa.accept_16_8_5_3_1_4297
  72 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 275 (accept_3_2 70 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 275 (accept_3_2 67 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 275
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 65 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 275 (accept_3_2 64 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 275 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 275 (accept_3_2 61 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 275
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 275 (accept_3_2 58 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 275 (accept_3_2 55 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 275 (accept_3_2 52 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 275 (accept_3_2 49 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 275 (accept_3_2 46 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 275 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 275 (accept_3_2 43 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 275 (accept_3_2 40 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 275 (accept_3_2 37 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 275 (accept_3_2 34 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 275 (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 275 (accept_3_2 31 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 275 (accept_3_2 28 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 275 (accept_3_2 25 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 275
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 275 (accept_3_2 22 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 275 (accept_3_2 19 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 275 (accept_3_2 16 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 275 (accept_3_2 13 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 275
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 275 (accept_3_2 10 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 101 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 275 (accept_3_2 7 101 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 275 (accept_3_2 4 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 275 (accept_3_2 1 101 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 275 (allA_of_3_0 100 100 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 275 (allA_succ_of_accept 98 99
  275 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 275 (accept_3_2 97 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 96 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 275 (Polychromatic418967fa.accept_23_3_7_22_1_16917 95 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 275 (accept_3_2 94 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 275 (accept_3_2 91 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 275 (Polychromatic418967fa.accept_15_14_9_5_1_3932 89 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 275 11 8 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 99 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 275 (accept_3_2 85 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 83
  99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 275 (accept_3_2 82 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 275 (accept_3_2 79 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085 78 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 99 275 11 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 99 275 (accept_3_2 76 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 75 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 275 (accept_3_2 73 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 275 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 275 (accept_3_2 70 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 275 (accept_3_2 67 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99
  275 11 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  99 275 (Polychromatic418967fa.accept_19_8_4_9_1_10244 65 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 99 275 (accept_3_2 64 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 99 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 275 (accept_3_2 61 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 275
  (Polychromatic418967fa.accept_21_18_15_2_1_4806 60 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 99 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 275 (accept_3_2 58 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 99 275 11 5 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 99 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 275 (Polychromatic418967fa.accept_17_2_14_3_1_4679 53 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 275 (accept_3_2 52 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 51
  99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 275 (accept_3_2 49 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 275 (Polychromatic418967fa.accept_23_1_7_22_1_12002 47 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 275 (accept_3_2 46 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 99 275 11 4 9 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 275 (accept_3_2 43 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973
  42 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 275 (accept_3_2 40 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 275 (Polychromatic418967fa.accept_21_18_15_2_1_4806 39 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 275 (accept_3_2 37 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 275
  (Polychromatic418967fa.accept_19_16_4_9_1_10196 35 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 275 (accept_3_2 34 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99
  275 11 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 275 (accept_3_2 31 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 275 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 275 (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 275 (accept_3_2 28 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 275 (accept_3_2 25 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 275 11 2 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 99 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 275 (accept_3_2 19 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 275 (accept_3_2 16 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 275
  (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 275 (accept_3_2 13 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 275 11 1 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 275 (accept_3_2 10 99 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 275 (accept_3_2 7 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 275 (Polychromatic418967fa.accept_19_5_4_9_1_4563 5 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 275 (accept_3_2 4 99 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 275 (accept_3_2 1 99 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  275 (allA_succ_of_accept 97 98 275 (accept_3_2 97 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 275 (Polychromatic418967fa.accept_16_15_2_3_1_4262 95 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 275 (accept_3_2 94 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 275 (accept_3_2 91 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 275 (Polychromatic418967fa.accept_19_14_3_9_1_2157 90 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 275 (accept_3_2 88 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 275
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 86 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 275 (accept_3_2 85 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 275 (accept_3_2 82 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 275 (accept_3_2 79 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 275 (accept_3_2 76 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 275 (accept_3_2 73 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 275 (accept_3_2 70 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 275 (accept_3_2 67 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 275 (accept_3_2 64 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 275 (accept_3_2 61 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 275 (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 275 (accept_3_2 58 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 275 (accept_3_2 55 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 275 (Polychromatic418967fa.accept_16_6_2_3_1_4223 54 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 275 (accept_3_2 52 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 275
  (Polychromatic418967fa.accept_17_16_13_3_1_4677 50 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 275 (accept_3_2 49 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 275 (accept_3_2 46 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 275 (accept_3_2 43 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 275 (accept_3_2 40 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 275 (accept_3_2 37 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 275 (Polychromatic418967fa.accept_20_16_18_15_1_11357 36 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 275 (accept_3_2 34 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 275 (accept_3_2 31 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 275 (accept_3_2 28 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 275 (accept_3_2 25 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 275 (accept_3_2 22 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 275 (accept_3_2 19 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 275 (accept_3_2 16 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 275
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 275 (accept_3_2 13 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 275 (accept_3_2 10 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 275 (accept_3_2 7 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 275 (accept_3_2 4 98 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 275 (accept_3_2 1 98 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  275 (allA_of_3_0 97 97 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 275 (allA_succ_of_accept 95 96 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 275 (accept_3_2 94 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 275 (accept_3_2 91 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 275 (Polychromatic418967fa.accept_13_12_5_2_1_2173 90 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 275 (accept_3_2 88 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 86 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 275 (accept_3_2 85 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 96 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 275 (accept_3_2 82 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 275 (accept_3_2 79 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 78 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 275
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 275 (accept_3_2 76 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 275 (accept_3_2 73 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 275 (accept_3_2 70 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 275 (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 275 (accept_3_2 67 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 275 (accept_3_2 64 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 275 (Polychromatic418967fa.accept_14_7_12_9_1_2926 63 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 275 (accept_3_2 61 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 275 (accept_3_2 58 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 275 (accept_3_2 55 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 275 (accept_3_2 52 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 275 (Polychromatic418967fa.accept_19_12_1_9_1_10281 50 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 275 (accept_3_2 49 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 96 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 275 (accept_3_2 46 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 275 (accept_3_2 43 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 275 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 275
  (Polychromatic418967fa.accept_10_1_6_5_1_304 41 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 275 (accept_3_2 40 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 275 (accept_3_2 37 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 275 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 275 (accept_3_2 34 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 275 (accept_3_2 31 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 275 (accept_3_2 28 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 275 (accept_3_2 25 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 275
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 275 (accept_3_2 22 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 275 (accept_3_2 19 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 275 (accept_3_2 16 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 275 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 275 (accept_3_2 13 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 275 (accept_3_2 10 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 275 (accept_3_2 7 96 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 275 (Polychromatic418967fa.accept_21_6_12_2_1_4801 6 96 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 275
  (Polychromatic418967fa.accept_19_5_1_9_1_8895 5 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 275 (accept_3_2 4 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 275 (accept_3_2 1 96 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 275
  (allA_succ_of_accept 94 95 275 (accept_3_2 94 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 275 (Polychromatic418967fa.accept_16_13_15_3_1_4196 93 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 92 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 275 (accept_3_2 91 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 275 5 18 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 275 (accept_3_2 88 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 275 (Polychromatic418967fa.accept_16_7_15_3_1_1302
  87 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 275
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 86 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 275 5 17 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 275 (accept_3_2 82 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 275
  (Polychromatic418967fa.accept_17_13_10_3_1_7136 81 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 95 275 5 16 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 95 275 (accept_3_2 79 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  95 275 (Polychromatic418967fa.accept_22_12_7_11_1_15439 78 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 95 275 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 275 (accept_3_2 76 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 95 275 5 15 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 95 275
  (Polychromatic418967fa.accept_24_2_23_11_1_16916 74 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 95 275 (accept_3_2 73 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 95 275 (Polychromatic418967fa.accept_14_2_11_9_1_2925 72 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 275 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 95 275 5 14 19 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 95 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 95 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 275 (accept_3_2 67 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 95 275 (Polychromatic418967fa.accept_16_2_15_3_1_1300 66 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 275 5 13 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 275 (accept_3_2 64 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  63 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 275 (accept_3_2 61 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 95
  275 5 12 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  95 275 (Polychromatic418967fa.accept_16_11_15_3_1_1304 59 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 95 275 (accept_3_2 58 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 95 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 57 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 275 (Polychromatic418967fa.accept_21_14_11_2_1_13897 56 95
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 95 275 5 11 19 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 95 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 95 275 (Polychromatic418967fa.accept_23_7_3_22_1_7056 53 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 275 (accept_3_2 52 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 95 275 (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 275 5 10 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 275 (accept_3_2 49 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 275 (accept_3_2 46 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 95
  275 5 9 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  95 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 95 275 (accept_3_2 43 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 95 275 (Polychromatic418967fa.accept_23_19_3_22_1_13660 42 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 95 275 5 8 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 275
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 39 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 275 (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 275 (accept_3_2 37 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 275 5 7 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 275 (accept_3_2 34 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 275
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 275 (accept_3_2 31 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95
  275 5 6 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  95 275 (Polychromatic418967fa.accept_16_13_15_3_1_4196 29 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 275 (accept_3_2 28 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 275 5 5 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 275
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 275 (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 275 (accept_3_2 22 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 275 (Polychromatic418967fa.accept_22_21_7_11_1_7486 21 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 275 5 4 19 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 275 (accept_3_2 19 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 95 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 275
  (Polychromatic418967fa.accept_21_17_11_2_1_7953 17 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 275 (accept_3_2 16 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95
  275 5 3 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  95 275 (Polychromatic418967fa.accept_21_14_11_2_1_13897 14 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 95 275 (accept_3_2 13 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 95 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 95
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 95 275 5 2 19 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 275
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 275 (Polychromatic418967fa.accept_26_8_17_15_1_16915 8 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 275 (accept_3_2 7 95 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 275 5 1 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 275 (accept_3_2 4 95 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 275 (Polychromatic418967fa.accept_24_3_23_11_1_8429 3 95 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 275
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 2 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 275 (accept_3_2 1 95 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 275
  (allA_of_3_0 94 94 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 275 (allA_succ_of_accept 92 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 275 (accept_3_2 91 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 275 (accept_3_2 88 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 275 (accept_3_2 85 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 84 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 275 (accept_3_2 82 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 81 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 275 (accept_3_2 79 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 275 (accept_3_2 76 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 275 (accept_3_2 73 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 275 (accept_3_2 70 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 275 (accept_3_2 67 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 275 (accept_3_2 64 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 275 (accept_3_2 61 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 275 (Polychromatic418967fa.accept_19_2_17_9_1_10317 59 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 275 (accept_3_2 58 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 93 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 275 (accept_3_2 55 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 275 (accept_3_2 52 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 275 (accept_3_2 49 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 275 (accept_3_2 46 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 275 (Polychromatic418967fa.accept_19_7_17_9_1_8879 45 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 275 (accept_3_2 43 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 275 (Polychromatic418967fa.accept_21_20_9_2_1_15500 41 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 275 (accept_3_2 40 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 93 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 275 (accept_3_2 37 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 275 (accept_3_2 34 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 275 (accept_3_2 31 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 275 (accept_3_2 28 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 275 (accept_3_2 25 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 275 (Polychromatic418967fa.accept_15_8_3_5_1_608 23 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 275 (accept_3_2 22 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 275 (accept_3_2 19 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 275 (accept_3_2 16 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 275 (accept_3_2 13 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 275 (accept_3_2 10 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 93 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 275 (accept_3_2 7 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 275 (Polychromatic418967fa.accept_17_5_8_3_1_1419 5 93 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 275 (accept_3_2 4 93 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 275 (accept_3_2 1 93 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 275
  (allA_succ_of_accept 91 92 275 (accept_3_2 91 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 275 (accept_3_2 88 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 275 (accept_3_2 85 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 275 (accept_3_2 82 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 275 (accept_3_2 79 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 77 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 275 (accept_3_2 76 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 275 (accept_3_2 73 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 275 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 275 (accept_3_2 70 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 275
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 275 (accept_3_2 67 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 275 (Polychromatic418967fa.accept_19_8_16_9_1_8847 65 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 275 (accept_3_2 64 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 275 (accept_3_2 61 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 275 (accept_3_2 58 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 275 (accept_3_2 55 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 275 (Polychromatic418967fa.accept_22_10_4_11_1_16914 54 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 275 (accept_3_2 52 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 275 (accept_3_2 49 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 275 (accept_3_2 46 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 275 (accept_3_2 43 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 275 (accept_3_2 40 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 275 (accept_3_2 37 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 275 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 275 (accept_3_2 34 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 275
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 275 (accept_3_2 31 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 275 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 275 (accept_3_2 28 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 275 (accept_3_2 25 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 275 (accept_3_2 22 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 275 (accept_3_2 19 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 275 (accept_3_2 16 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 275 (accept_3_2 13 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 275 (accept_3_2 10 92 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 275 (accept_3_2 7 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 275 (Polychromatic418967fa.accept_20_5_12_15_1_9860 5 92 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 275 (accept_3_2 4 92 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  92 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 275 (accept_3_2 1 92 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 275
  (allA_of_3_0 91 91 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 275 (allA_succ_of_accept 89 90 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 275 (accept_3_2 88 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 275 (Polychromatic418967fa.accept_20_6_10_15_1_6879 86 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 90 275 5 17 18 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 90 275
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 83 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 275 (accept_3_2 82 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 275 5 16 18 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 275 (accept_3_2 79 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 275 (accept_3_2 76 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90
  275 5 15 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74
  90 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 90 275 (accept_3_2 73 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 275 (Polychromatic418967fa.accept_20_12_10_15_1_9869 72 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 275 5 14 18 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 90 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 68 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 275 (accept_3_2 67 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 90 275 5 13 18 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 275 (accept_3_2 64 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 275 (Polychromatic418967fa.accept_19_6_14_9_1_8863 63 90
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 275
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 62 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 275 (accept_3_2 61 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90
  275 5 12 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 275 (accept_3_2 58 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 90
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 275 5 11 18 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 90 275
  (Polychromatic418967fa.accept_19_16_14_9_1_7316 54 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 275 (accept_3_2 52 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 275 (Polychromatic418967fa.accept_20_11_10_15_1_11318 51 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 275 5 10 18 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 275 (accept_3_2 49 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 275
  (Polychromatic418967fa.accept_20_8_10_15_1_6922 48 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 275 (Polychromatic418967fa.accept_20_7_10_15_1_14095 47 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 275 (accept_3_2 46 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 90 275 5 9 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 90 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 275 (accept_3_2 43 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 275 5 8 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 275 (accept_3_2 37 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 90 275 5 7 18 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 275 (accept_3_2 34
  90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 90 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 275 (accept_3_2 31 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 90 275 5 6 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 275 (accept_3_2 28 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 275 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 275
  (Polychromatic418967fa.accept_20_6_10_15_1_6879 26 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 90 275 5 5 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 90
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 275 (accept_3_2 22 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 275 5 4 18 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 275 (accept_3_2 19
  90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 275 (accept_3_2 16 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 90 275 5 3 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 90 275 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 275 (accept_3_2 13 90 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 275 (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 90 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 275 5 2 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 275 (accept_3_2 7 90 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 275 (Polychromatic418967fa.accept_13_6_12_2_1_4707
  6 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 90 275 5 1 18 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 275 (accept_3_2 4 90
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 275 (Polychromatic418967fa.accept_7_3_6_2_1_90
  3 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 275
  (Polychromatic418967fa.accept_17_2_5_3_1_1416 2 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 275 (accept_3_2 1 90 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 275
  (allA_succ_of_accept 88 89 275 (accept_3_2 88 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 275 (accept_3_2 85 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 275 (accept_3_2 82 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 275 (accept_3_2 79 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 275
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 77 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 275 (accept_3_2 76 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 275 (accept_3_2 73 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 275 (Polychromatic418967fa.accept_19_15_13_9_1_7324 72 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 275 (accept_3_2 70 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 275 (Polychromatic418967fa.accept_13_3_11_2_1_1422 68 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 275 (accept_3_2 67 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 275 (accept_3_2 64 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 275 (Polychromatic418967fa.accept_14_7_5_9_1_2911 63 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 275 (accept_3_2 61 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 275 (accept_3_2 58 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 275 (accept_3_2 55 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 275 (accept_3_2 52 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 275 (accept_3_2 49 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 275 (accept_3_2 46 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 44 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 275 (accept_3_2 43 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 275 (accept_3_2 40 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 275 (accept_3_2 37 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 275
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 275 (accept_3_2 34 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 275 (accept_3_2 31 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 275 (accept_3_2 28 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 275 (Polychromatic418967fa.accept_24_3_17_11_1_6582 27 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 275 (accept_3_2 25 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 275
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 275 (accept_3_2 22 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 275 (accept_3_2 19 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 275 (accept_3_2 16 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 275 (accept_3_2 13 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 275 (accept_3_2 10 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 275 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 275 (accept_3_2 7 89 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 275
  (Polychromatic418967fa.accept_19_5_13_9_1_5957 5 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 275 (accept_3_2 4 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 275 (accept_3_2 1 89 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 275 (allA_of_3_0 88 88 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 275
  (allA_succ_of_accept 86 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 275 (accept_3_2 85 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 83
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 275 (accept_3_2 82 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 275
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 275 (accept_3_2 79 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107
  77 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 275 (accept_3_2 76
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 275 (accept_3_2 73 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 71
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 275 (accept_3_2 70 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 275 (accept_3_2 67 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 65
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 275 (accept_3_2 64 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 275 (accept_3_2 61 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 275 (Polychromatic418967fa.accept_13_7_9_2_1_2167
  59 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 275 (accept_3_2 58
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 275 (accept_3_2 55 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 275 (accept_3_2 52 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 275
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 275 (accept_3_2 49 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 275 (accept_3_2 46 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 275
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 275 (accept_3_2 43 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 275 (accept_3_2 40 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 275 (Polychromatic418967fa.accept_9_3_6_5_1_63
  39 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 275 (accept_3_2 37 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 275 (accept_3_2 34 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 275 (accept_3_2 31 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 275 (accept_3_2 28 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 275 (accept_3_2 25 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 275 (accept_3_2 22 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 275 (accept_3_2 19 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 275 (accept_3_2 16 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 275 (accept_3_2 13 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 275 (accept_3_2 10 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 275 (accept_3_2 7 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 275 (accept_3_2 4 87 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 275 (accept_3_2 1 87 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 275
  (allA_succ_of_accept 85 86 275 (accept_3_2 85 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 83 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 275 (accept_3_2 82 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 275 (accept_3_2 79 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 275 (Polychromatic418967fa.accept_29_20_28_14_1_16913 78 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 275 (accept_3_2 76 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 74 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 275 (accept_3_2 73 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 275 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 71 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 275 (accept_3_2 70 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 275 (accept_3_2 67 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 66 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 275 (accept_3_2 64 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 275
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 62 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 275 (accept_3_2 61 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 275 (accept_3_2 58 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 275 (accept_3_2 55 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 275 (accept_3_2 52 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 275
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 50 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 275 (accept_3_2 49 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 275 (Polychromatic418967fa.accept_26_22_8_15_1_16912 48 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 275 (accept_3_2 46 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 275 (accept_3_2 43 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 275 (Polychromatic418967fa.accept_19_4_10_9_1_4569 42 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 275 (accept_3_2 40 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 275
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 275 (accept_3_2 37 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 275 (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 275 (accept_3_2 34 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 275 (accept_3_2 31 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 275 (Polychromatic418967fa.accept_20_10_6_15_1_5381 30 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 275 (accept_3_2 28 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 275
  (Polychromatic418967fa.accept_17_9_1_3_1_4626 26 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 275 (accept_3_2 25 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 275 (accept_3_2 22 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 275 (accept_3_2 19 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 275 (accept_3_2 16 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 275 (accept_3_2 13 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 275 (Polychromatic418967fa.accept_19_12_10_9_1_3326 12 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 275 (accept_3_2 10 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 275 (accept_3_2 7 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  275 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 86 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 275 (accept_3_2 4 86 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 275
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 275 (accept_3_2 1 86 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 275
  (allA_of_3_0 85 85 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 275 (allA_succ_of_accept 83 84 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 275 (accept_3_2 82 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 275 (accept_3_2 79 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 275
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 275 (accept_3_2 76 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 275 (Polychromatic418967fa.accept_13_10_6_2_1_1440 75 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 275 (accept_3_2 73 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 275 (accept_3_2 70 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 275 (Polychromatic418967fa.accept_19_11_8_9_1_5993 68 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 275 (accept_3_2 67 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 275 (accept_3_2 64 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 275 (accept_3_2 61 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 275
  (Polychromatic418967fa.accept_10_9_4_5_1_616 59 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 275 (accept_3_2 58 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 275 (accept_3_2 55 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 275 (Polychromatic418967fa.accept_16_6_4_3_1_2189 54 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 275 (accept_3_2 52 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 275 (Polychromatic418967fa.accept_20_10_4_15_1_12657 50 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 275 (accept_3_2 49 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 84 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 275 (accept_3_2 46 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 275 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 275 (accept_3_2 43 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 275
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 275 (accept_3_2 40 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 275 (accept_3_2 37 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 275 (accept_3_2 34 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 275 (Polychromatic418967fa.accept_22_10_18_11_1_15425 32 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 275 (accept_3_2 31 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 275 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 84 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 275 (accept_3_2 28 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 275 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 275 (accept_3_2 25 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 275 (accept_3_2 22 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 275 (accept_3_2 19 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 275 (accept_3_2 16 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 275 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 275 (accept_3_2 13 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 275 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 275 (accept_3_2 10 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 275 (accept_3_2 7 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 275
  (Polychromatic418967fa.accept_20_5_4_15_1_3931 5 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 275 (accept_3_2 4 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 84 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 275 (accept_3_2 1 84 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 275
  (allA_succ_of_accept 82 83 275 (accept_3_2 82 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 275 (accept_3_2 79 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 275
  (Polychromatic418967fa.accept_10_7_3_5_1_301 77 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 275 (accept_3_2 76 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 275 (accept_3_2 73 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 275 (accept_3_2 70 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 68 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 275 (accept_3_2 67 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 275
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 65 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 275 (accept_3_2 64 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 275 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 275 (accept_3_2 61 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 275 (accept_3_2 58 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 275 (Polychromatic418967fa.accept_13_4_5_2_1_1436 56 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 275 (accept_3_2 55 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 275 (Polychromatic418967fa.accept_19_16_7_9_1_7321 54 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 275 (accept_3_2 52 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 275 (accept_3_2 49 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 275
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 275 (accept_3_2 46 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 275 (accept_3_2 43 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 275 (accept_3_2 40 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 275 (accept_3_2 37 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 275 (accept_3_2 34 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 275 (accept_3_2 31 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 275 (accept_3_2 28 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 275 (accept_3_2 25 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 275
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 275 (accept_3_2 22 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 275 (accept_3_2 19 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 275 (accept_3_2 16 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 275 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 275 (accept_3_2 13 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 275 (accept_3_2 10 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 275 (accept_3_2 7 83 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 275
  (Polychromatic418967fa.accept_19_5_7_9_1_5954 5 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 275 (accept_3_2 4 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 83 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 275 (accept_3_2 1 83 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 275 (allA_of_3_0 82 82 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 275
  (allA_succ_of_accept 80 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 275 (accept_3_2 79 81 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470
  77 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 275 (accept_3_2 76
  81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 275 (accept_3_2 73 81 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 275 (Polychromatic418967fa.accept_14_2_11_9_1_2925 72 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 275
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 275 (accept_3_2 70 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 275 (accept_3_2 67 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 275
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 65 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 275 (accept_3_2 64 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 275 (accept_3_2 61 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 275 (Polychromatic418967fa.accept_22_16_15_11_1_16911 60 81 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 275
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 275 (accept_3_2 58 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 275 (accept_3_2 55 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 275
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 275 (accept_3_2 52 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 275 (accept_3_2 49 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 275 (accept_3_2 46 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 275 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 275 (accept_3_2 43 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 275 (accept_3_2 40 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 275 (accept_3_2 37 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 275
  (Polychromatic418967fa.accept_13_9_3_2_1_399 35 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 275 (accept_3_2 34 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 275 (accept_3_2 31 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 275
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 275 (accept_3_2 28 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 275 (accept_3_2 25 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 275
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 275 (accept_3_2 22 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 275 (Polychromatic418967fa.accept_17_4_13_3_1_7166 21 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 275 (accept_3_2 19 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 275
  (Polychromatic418967fa.accept_22_17_15_11_1_9158 17 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 81 275 (accept_3_2 16 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 81 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 275 (accept_3_2 13 81 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 275
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 275 (accept_3_2 10 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 275 (accept_3_2 7 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 275 (accept_3_2 4 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 275 (accept_3_2 1 81 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 275 (allA_succ_of_accept 79 80 275 (accept_3_2 79 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 275 (Polychromatic418967fa.accept_21_14_17_2_1_11069 77 80
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 275 (accept_3_2 76 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 275 5 15 16 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 275 (accept_3_2 73 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 275 (Polychromatic418967fa.accept_19_15_4_9_1_11608 72 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 275 5 14 16 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 80 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 275 (accept_3_2 67 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 80 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 275 5 13 16 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 275 (accept_3_2 64 80 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 275 (accept_3_2 61 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  275 5 12 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 275 (Polychromatic418967fa.accept_17_8_12_3_1_5927 59 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 80 275 (accept_3_2 58 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 80 275 5 11 16 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 80 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 80 275 (Polychromatic418967fa.accept_18_17_8_5_1_2769 53 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 275 (accept_3_2 52 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 275 5 10 16 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 275 (accept_3_2 49 80 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 80 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 80 275 (accept_3_2 46 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 80
  275 5 9 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  80 275 (Polychromatic418967fa.accept_27_17_26_5_1_16910 44 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 80 275 (accept_3_2 43 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 80 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 275 5 8 16 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 80 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 275 (accept_3_2 37 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 80 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 80 275 5 7 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 80 275 (accept_3_2 34 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 275
  (Polychromatic418967fa.accept_17_15_12_3_1_8478 32 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 275 (accept_3_2 31 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  275 5 6 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 80 275 (accept_3_2 28 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 80 275 5 5 16 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 80 275
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 80 275 (Polychromatic418967fa.accept_22_1_14_11_1_13766 23 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 275 (accept_3_2 22 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 275 5 4 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 275 (accept_3_2 19 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 275 (Polychromatic418967fa.accept_24_18_8_11_1_10125 18 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 275
  (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 275 (accept_3_2 16 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 80
  275 5 3 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  80 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 80 275 (accept_3_2 13 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 80 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 275 5 2 16 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 275 (accept_3_2 7 80 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 275 5 1 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 275 (accept_3_2 4 80 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 275 (accept_3_2 1 80 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 275 (allA_of_3_0 79
  79 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 275 (allA_succ_of_accept 77 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 275 (accept_3_2 76 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 275 (accept_3_2 73 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 275 (accept_3_2 70 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 275 (Polychromatic418967fa.accept_15_8_3_5_1_608 68 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 275 (accept_3_2 67 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 275 (accept_3_2 64 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 275 (accept_3_2 61 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 275 (Polychromatic418967fa.accept_17_9_10_3_1_3423 60 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 275 (accept_3_2 58 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 275 (accept_3_2 55 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 275 (accept_3_2 52 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 275 (Polychromatic418967fa.accept_19_12_2_9_1_15638 50 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 275 (accept_3_2 49 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 275 (accept_3_2 46 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 275 (accept_3_2 43 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 275 (accept_3_2 40 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 275 (accept_3_2 37 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 275 (accept_3_2 34 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 275 (accept_3_2 31 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 275 (accept_3_2 28 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 275 (accept_3_2 25 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 275
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 275 (accept_3_2 22 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 275 (accept_3_2 19 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 275 (Polychromatic418967fa.accept_19_18_2_9_1_8870 18 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 275 (accept_3_2 16 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 275 (Polychromatic418967fa.accept_14_1_8_9_1_1312 15 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 275 (Polychromatic418967fa.accept_22_14_12_11_1_9182 14 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 275 (accept_3_2 13 78 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 78 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 275 (accept_3_2 10 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 275 (accept_3_2 7 78 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 275 (accept_3_2 4 78 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 275 (accept_3_2 1 78 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 275
  (allA_succ_of_accept 76 77 275 (accept_3_2 76 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 75 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 275 (accept_3_2 73 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 275
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 275 (accept_3_2 70 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 69 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 275 (accept_3_2 67 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 77 275 11 6 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 77 275 (Polychromatic418967fa.accept_16_1_13_3_1_2168 65 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 275 (accept_3_2 64 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 77 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 275 (accept_3_2 61 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 275 (Polychromatic418967fa.accept_23_14_8_22_1_13662 60 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 275 (accept_3_2 58 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 77
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 275
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 77 275 11 5 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 275 (accept_3_2 52 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 275 (Polychromatic418967fa.accept_21_9_14_2_1_6370
  51 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 275 (accept_3_2 49 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 275 (accept_3_2 46 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 275 (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 275 11 4 7 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 275 (accept_3_2 43 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 275 (accept_3_2 40 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 275 (Polychromatic418967fa.accept_20_19_17_15_1_2690 39 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 275 (accept_3_2 37 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 275
  (Polychromatic418967fa.accept_17_1_9_3_1_7161 35 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 275 (accept_3_2 34 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77
  275 11 3 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  77 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 77 275 (accept_3_2 31 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 275 (accept_3_2 28 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 275 (Polychromatic418967fa.accept_13_1_12_2_1_384
  27 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 275 (accept_3_2 25 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 275 (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 77 275 11 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 77 275 (Polychromatic418967fa.accept_19_2_1_9_1_10240
  21 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 275
  (Polychromatic418967fa.accept_21_20_14_2_1_6393 20 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 275 (accept_3_2 19 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 275 (accept_3_2 16 77 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 275 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 77
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 275 (accept_3_2 13 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 77 275 11 1 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 77 275 (accept_3_2 10 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 77 275 (Polychromatic418967fa.accept_21_9_14_2_1_6370 9 77 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 275 (accept_3_2 7 77 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 275
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 275 (accept_3_2 4 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  275 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 77 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 275 (accept_3_2 1 77 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 275 (allA_of_3_0 76 76 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 275 (allA_succ_of_accept 74 75
  275 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 275 (accept_3_2 73 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 275 (Polychromatic418967fa.accept_16_8_11_3_1_4279 72 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 275 5 14 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 275
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 275 (accept_3_2 67 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 275 5 13 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 275 (accept_3_2 64 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 275 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 75
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 275 (accept_3_2 61 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  275 5 12 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 275 (accept_3_2 58 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 275 5 11 15 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 275
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 275 (accept_3_2 52 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 275 25 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 275 (accept_3_2 49 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 275 (Polychromatic418967fa.accept_19_10_18_9_1_11636 48 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 275 (accept_3_2 46 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  275 5 9 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 275 (accept_3_2 43 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 275 (Polychromatic418967fa.accept_19_3_18_9_1_4580 41 75
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 275 5 8 15 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 275 (accept_3_2 37 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 275 (Polychromatic418967fa.accept_22_14_9_11_1_16907 36 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 275 5 7 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 275 (accept_3_2 34 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 275 (accept_3_2 31 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  275 5 6 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 275 (accept_3_2 28 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 275 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 275 25 1 3 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 275 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 275 (accept_3_2 22 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 275 5 4 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 275 (accept_3_2 19 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 275 (accept_3_2 16 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  275 5 3 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 275 (accept_3_2 13 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 275 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 275 5 2 15 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 275
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 275 (accept_3_2 7 75 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 275 5 1 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 275 (accept_3_2 4 75 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 275 (accept_3_2 1 75 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 275 (allA_succ_of_accept
  73 74 275 (accept_3_2 73 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 275
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 275 (accept_3_2 70 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 68
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 275 (accept_3_2 67 74
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 275 (accept_3_2 64 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 275 (accept_3_2 61 74
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 59 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 275 (accept_3_2 58 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 275 (Polychromatic418967fa.accept_10_6_4_5_1_615
  56 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 275 (accept_3_2 55
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 275 (accept_3_2 52 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969
  50 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 275 (accept_3_2 49
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 275 (accept_3_2 46 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 44
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 275 (accept_3_2 43 74
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 275 (accept_3_2 40 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089
  38 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 275 (accept_3_2 37
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 275 (accept_3_2 34 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 275 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 275 (accept_3_2 31
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 275 (accept_3_2 28 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 275 (accept_3_2 25 74
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 275 (accept_3_2 22 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 275 (accept_3_2 19 74
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 275 (accept_3_2 16 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  14 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 275 (accept_3_2 13
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 275 (accept_3_2 10 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 275 (accept_3_2 7 74 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 275 (accept_3_2 4 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 275 (accept_3_2 1 74 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  275 (allA_of_3_0 73 73 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 275 (allA_succ_of_accept 71 72 275
  (Polychromatic418967fa.accept_22_5_6_11_1_12251 71 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 275 (accept_3_2 70 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 275 (accept_3_2 67 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 275
  (Polychromatic418967fa.accept_20_5_12_15_1_9860 65 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 275 (accept_3_2 64 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107 62 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 275 (accept_3_2 61 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 275 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 72 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 275
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 59 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 275 (accept_3_2 58 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 275 (Polychromatic418967fa.accept_19_18_15_9_1_3310 56 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 275 (accept_3_2 55 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 54 72
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 275 (accept_3_2 52 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 275 (Polychromatic418967fa.accept_17_16_4_3_1_3429 50 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 275 (accept_3_2 49 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 72 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 275
  (Polychromatic418967fa.accept_10_7_2_5_1_298 47 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 275 (accept_3_2 46 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 275 (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 275 (accept_3_2 43 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 275 (Polychromatic418967fa.accept_19_4_15_9_1_8845 42 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 275
  (Polychromatic418967fa.accept_17_7_4_3_1_3456 41 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 275 (accept_3_2 40 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 275 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 275 (accept_3_2 37 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 275
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 275 (accept_3_2 34 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 275 (accept_3_2 31 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 275 (Polychromatic418967fa.accept_17_13_4_3_1_1446 30 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 275
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 29 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 275 (accept_3_2 28 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 275 (Polychromatic418967fa.accept_20_6_12_15_1_3938 26 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 275 (accept_3_2 25 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 72
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 275 (accept_3_2 22 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 275 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 275 (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 275 (accept_3_2 19 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 275
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 275 (accept_3_2 16 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 275 (Polychromatic418967fa.accept_21_15_9_2_1_7973 15 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 275 (Polychromatic418967fa.accept_21_14_9_2_1_8005 14 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 275 (accept_3_2 13 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 275 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 72
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 275
  (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 275 (accept_3_2 10 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 275 (accept_3_2 7 72 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 72 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 275
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 275 (accept_3_2 4 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  275 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 72 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 72 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 275 (accept_3_2 1 72 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 275
  (allA_succ_of_accept 70 71 275 (accept_3_2 70 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 275 (accept_3_2 67 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 275 (accept_3_2 64 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 275 (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 275 (accept_3_2 61 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 275 (accept_3_2 58 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 275 (accept_3_2 55 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 275
  (Polychromatic418967fa.accept_13_1_6_2_1_377 53 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 275 (accept_3_2 52 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085 50 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 275 (accept_3_2 49 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 275 (accept_3_2 46 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 275 (accept_3_2 43 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 275 (accept_3_2 40 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 275 (accept_3_2 37 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 275
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 275 (accept_3_2 34 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 275 (accept_3_2 31 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 275 (accept_3_2 28 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 275 (accept_3_2 25 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 275
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 275 (accept_3_2 22 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 275 (accept_3_2 19 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 275 (Polychromatic418967fa.accept_22_18_5_11_1_16909 18 71 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 275 (accept_3_2 16 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 275 (accept_3_2 13 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 275 (accept_3_2 10 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 275 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 275 (accept_3_2 7 71 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 275
  (Polychromatic418967fa.accept_19_5_14_9_1_4554 5 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 275 (accept_3_2 4 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 71 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 275 (accept_3_2 1 71 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 275
  (allA_of_3_0 70 70 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 275 (allA_succ_of_accept 68 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 275 (accept_3_2 67 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 275 (accept_3_2 64 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 275 (accept_3_2 61 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 275 (accept_3_2 58 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 275 (accept_3_2 55 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 275 (accept_3_2 52 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 275 (accept_3_2 49 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 275 (accept_3_2 46 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 275 (accept_3_2 43 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 275 (accept_3_2 40 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 275 (accept_3_2 37 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 275 (accept_3_2 34 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 275 (accept_3_2 31 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 275 (accept_3_2 28 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 275 (accept_3_2 25 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 275 (Polychromatic418967fa.accept_17_6_1_3_1_8503 23 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 275 (accept_3_2 22 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 275 (accept_3_2 19 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 275 (accept_3_2 16 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 275 (accept_3_2 13 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 275 (accept_3_2 10 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 275 (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 69 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 275 (accept_3_2 7 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 69 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 275 (accept_3_2 4 69 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 275 (accept_3_2 1 69 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 275 (allA_succ_of_accept 67 68
  275 (accept_3_2 67 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 275 (Polychromatic418967fa.accept_16_1_4_3_1_3148 65 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 275 (accept_3_2 64 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 275 (Polychromatic418967fa.accept_10_2_8_5_1_587
  62 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 275 (accept_3_2 61
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 275 (accept_3_2 58 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278
  56 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 275 (accept_3_2 55
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 275
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 54 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 275 (accept_3_2 52 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 275 (Polychromatic418967fa.accept_12_2_8_11_1_31
  50 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 275 (accept_3_2 49
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 275
  (Polychromatic418967fa.accept_13_9_3_2_1_399 48 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 275 (accept_3_2 46 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499
  44 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 275 (accept_3_2 43
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 275 (accept_3_2 40 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 275 (accept_3_2 37 68
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 275
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 275 (accept_3_2 34 68 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 275 (accept_3_2 31 68
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 275
  (Polychromatic418967fa.accept_20_10_8_15_1_11332 30 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 275 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 275 (accept_3_2 28 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 275 (accept_3_2 25 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 275 (accept_3_2 22 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 275
  (Polychromatic418967fa.accept_19_1_11_9_1_10307 20 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 275 (accept_3_2 19 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 275 (accept_3_2 16 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 275 (accept_3_2 13 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 275 (accept_3_2 10 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 275
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 275 (accept_3_2 7 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  275 (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 68 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 275 (accept_3_2 4 68 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 275 (accept_3_2 1 68 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 275 (allA_of_3_0 67 67 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 275 (allA_succ_of_accept 65 66 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 275 (accept_3_2 64 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 275 (accept_3_2 61 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 275
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 275 (accept_3_2 58 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 66 275 11 5 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 66 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54
  66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 275 (accept_3_2 52 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 275 (accept_3_2 49 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 275 (accept_3_2 46 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 66 275 11 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 275 (accept_3_2 43 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 66 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 275 (accept_3_2 40 66 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  39 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 275 (accept_3_2 37 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  66 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 66 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 275 (accept_3_2 34 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 275 11 3 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 66 275 (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 66 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 275 (accept_3_2 31 66 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 275 (Polychromatic418967fa.accept_20_10_6_15_1_5381 30 66
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 275 (accept_3_2 28 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 275 (accept_3_2 25 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 275
  (Polychromatic418967fa.accept_29_23_8_14_1_16908 23 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 66 275 11 2 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 275 (accept_3_2 19 66
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 275
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 275 (accept_3_2 16 66 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 275 (accept_3_2 13 66
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 66 275 11 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 66 275 (accept_3_2 10 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 275 (accept_3_2 7 66 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 275 (accept_3_2 4 66 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 275 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3
  66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 275 (accept_3_2 1 66 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 275 (allA_succ_of_accept 64 65 275
  (accept_3_2 64 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 275
  (Polychromatic418967fa.accept_20_3_5_15_1_2644 63 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 275 (accept_3_2 61 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 65 275 5 12 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 65 275 (Polychromatic418967fa.accept_20_19_5_15_1_5380 59 65 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 275 (accept_3_2 58 65 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 275
  (Polychromatic418967fa.accept_19_18_8_9_1_3325 56 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 275 5 11 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 275 (accept_3_2 52 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 275 5 10 13 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 275 (accept_3_2 49
  65 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 275 (Polychromatic418967fa.accept_20_7_5_15_1_1548 47 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 275 (accept_3_2 46 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 275 5 9 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 275 (accept_3_2 43 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 275
  (Polychromatic418967fa.accept_20_1_5_15_1_6913 41 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 275 5 8 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 275 (accept_3_2 37 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 275 (Polychromatic418967fa.accept_16_4_1_3_1_6581
  36 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 275 5 7 13 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 275 (accept_3_2 34
  65 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 275 (Polychromatic418967fa.accept_17_15_14_3_1_5947 32 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 275 (accept_3_2 31 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 275 5 6 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 275 (Polychromatic418967fa.accept_16_13_1_3_1_2205 29 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 275 (accept_3_2 28 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 275 (Polychromatic418967fa.accept_20_7_5_15_1_1548 27 65 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 275 5 5 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 275 (Polychromatic418967fa.accept_17_6_14_3_1_4678 23 65
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 275 (accept_3_2 22 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 275 5 4 13 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 275 (accept_3_2 19
  65 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 275 (accept_3_2 16 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 275 5 3 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 275 (accept_3_2 13 65 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 275
  (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 275 5 2 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 275 (Polychromatic418967fa.accept_20_9_5_15_1_3965 9 65 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 275 (accept_3_2 7 65 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 275 5 1 13 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 275 (accept_3_2 4 65
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 275 (Polychromatic418967fa.accept_9_3_2_5_1_234
  3 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 275 (accept_3_2 1 65 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 275 (allA_of_3_0 64 64 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 275 (allA_succ_of_accept 62 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 275 (accept_3_2 61 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 275 (Polychromatic418967fa.accept_16_11_15_3_1_1304 59 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 275 (accept_3_2 58 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 275 (accept_3_2 55 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 275 (Polychromatic418967fa.accept_14_12_7_9_1_726 54 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 275 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 275 (accept_3_2 52 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 275 (accept_3_2 49 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 275 (accept_3_2 46 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 275 (accept_3_2 43 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 275 (Polychromatic418967fa.accept_17_7_12_3_1_4693 41 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 275 (accept_3_2 40 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 275 (accept_3_2 37 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 275 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 275 (accept_3_2 34 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 275 (accept_3_2 31 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 275 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 275 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 275 (accept_3_2 28 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 275 (accept_3_2 25 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 275 (accept_3_2 22 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 275 (accept_3_2 19 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 275 (accept_3_2 16 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 275 (Polychromatic418967fa.accept_17_15_12_3_1_8478 15 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 275 (accept_3_2 13 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 275 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 275 (accept_3_2 10 63 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 275 (accept_3_2 7 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  275 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 63 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 63 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 275 (accept_3_2 4 63 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 275 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 63 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 275 (accept_3_2 1 63 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 275 (allA_succ_of_accept 61 62 275
  (accept_3_2 61 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 275 (accept_3_2 58 62 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 275 (accept_3_2 55 62
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 275
  (Polychromatic418967fa.accept_22_10_18_11_1_15425 54 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 275 (accept_3_2 52 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 275 (accept_3_2 49 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 275 (accept_3_2 46 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 275 (accept_3_2 43 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 275 (accept_3_2 40 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 275 (accept_3_2 37 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 275 (Polychromatic418967fa.accept_18_17_8_5_1_2769 35 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 275 (accept_3_2 34 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 275 (accept_3_2 31 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 275 (accept_3_2 28 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 275 (accept_3_2 25 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 275 (accept_3_2 22 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 275 (accept_3_2 19 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 275 (accept_3_2 16 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 275
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 275 (accept_3_2 13 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 275 (accept_3_2 10 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 275 (accept_3_2 7 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 275 (accept_3_2 4 62 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  62 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 275 (accept_3_2 1 62 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 275 (allA_of_3_0 61 61 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 275 (allA_succ_of_accept 59 60 275
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 275 (accept_3_2 58 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 275 5 11 12 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 275 (accept_3_2 52 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 275 (Polychromatic418967fa.accept_18_15_6_5_1_3972 51 60 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 275 5 10 12 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 275 (accept_3_2 49 60 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 275 (accept_3_2 46 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60
  275 5 9 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  60 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 275 (accept_3_2 43 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 275 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 275 5 8 12 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 275 (accept_3_2 37 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 60 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 275 5 7 12 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 275 (accept_3_2 34 60 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 275
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 275 (accept_3_2 31 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  275 5 6 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 275 (accept_3_2 28 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 275 5 5 12 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 275
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 275 (accept_3_2 22 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 275 5 4 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 275 (accept_3_2 19 60 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 275 (Polychromatic418967fa.accept_17_1_9_3_1_7161 18 60 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 275 (accept_3_2 16 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60
  275 5 3 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  60 275 (Polychromatic418967fa.accept_19_14_3_9_1_2157 14 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 275 (accept_3_2 13 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 275 5 2 12 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 275
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 275 (accept_3_2 7 60 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 60 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 275 5 1 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 275 (accept_3_2 4 60 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 275 (accept_3_2 1 60 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 275 (allA_succ_of_accept 58 59 275
  (accept_3_2 58 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 275 (accept_3_2 55 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089
  53 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 275 (accept_3_2 52
  59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 275 (accept_3_2 49 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47
  59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 275 (accept_3_2 46 59
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 275
  (Polychromatic418967fa.accept_19_7_2_9_1_6006 45 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 44 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 275 (accept_3_2 43 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 275 (Polychromatic418967fa.accept_19_4_2_9_1_4584 42 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 275 (accept_3_2 40 59
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 275
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 39 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 275 (Polychromatic418967fa.accept_15_8_14_5_1_2089 38 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 275 (accept_3_2 37 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  35 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 275 (accept_3_2 34
  59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 275 (accept_3_2 31 59 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 275 (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 59 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 275 (accept_3_2 28 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 275 (accept_3_2 25 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 275 (accept_3_2 22 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 275 (accept_3_2 19 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 59 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 275 (accept_3_2 16 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 275 (accept_3_2 13 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 275 (accept_3_2 10 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 275 (accept_3_2 7 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 275 (accept_3_2 4 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  275 (Polychromatic418967fa.accept_21_3_17_2_1_11043 3 59 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 275 (accept_3_2 1 59 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 275
  (allA_of_3_0 58 58 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 275 (allA_succ_of_accept 56 57 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 275 (accept_3_2 55 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 275 (accept_3_2 52 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 275 (accept_3_2 49 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 275 (accept_3_2 46 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 275 (accept_3_2 43 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 275 (accept_3_2 40 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 275 (accept_3_2 37 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 275 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 275 (accept_3_2 34 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 275 (accept_3_2 31 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 275 (accept_3_2 28 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 275 (accept_3_2 25 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 275 (accept_3_2 22 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 275 (accept_3_2 19 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 275 (accept_3_2 16 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 275 (accept_3_2 13 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 275 (accept_3_2 10 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 57 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 275 (accept_3_2 7 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 275 (Polychromatic418967fa.accept_17_5_6_3_1_4640 5 57 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 275 (accept_3_2 4 57 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 275 (accept_3_2 1 57 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 275 (allA_succ_of_accept 55 56 275 (accept_3_2 55 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 275 (accept_3_2 52 56 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 275 (accept_3_2 49 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 275 (accept_3_2 46 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 275 (accept_3_2 43 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 275 (accept_3_2 40 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 275 (accept_3_2 37 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 275 (accept_3_2 34 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 275
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 275 (accept_3_2 31 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 275 (accept_3_2 28 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 275 (accept_3_2 25 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 275 (accept_3_2 22 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 275
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 275 (accept_3_2 19 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 275 (accept_3_2 16 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 275 (accept_3_2 13 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 275 (accept_3_2 10 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 275 (accept_3_2 7 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 56 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 275 (accept_3_2 4 56 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 275 (accept_3_2 1 56 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 275 (allA_of_3_0 55 55 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 275
  (allA_succ_of_accept 53 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 275 (accept_3_2 52 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 275 (Polychromatic418967fa.accept_16_2_6_3_1_5396
  50 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 275 (accept_3_2 49
  54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 275
  (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 275 (Polychromatic418967fa.accept_22_3_10_11_1_12292 47 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 275 (accept_3_2 46 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 275 (Polychromatic418967fa.accept_15_14_9_5_1_3932
  44 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 275 (accept_3_2 43
  54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 275
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 275 (accept_3_2 40 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 275 (accept_3_2 37 54
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 275 (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 275 (accept_3_2 34 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 275 (accept_3_2 31 54
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 275
  (Polychromatic418967fa.accept_20_10_14_15_1_9885 30 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 275 (accept_3_2 28 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 54 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 275 (accept_3_2 25 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 275 (Polychromatic418967fa.accept_19_4_16_9_1_10315 23 54 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 275 (accept_3_2 22 54 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 275
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 20 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 275 (accept_3_2 19 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 275 (accept_3_2 16 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 275 (Polychromatic418967fa.accept_22_15_10_11_1_13816 15 54 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 275 (accept_3_2 13 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 275 (accept_3_2 10 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 275
  (Polychromatic418967fa.accept_19_8_16_9_1_8847 8 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 275 (accept_3_2 7 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  275 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 275 (accept_3_2 4 54 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 275 (Polychromatic418967fa.accept_16_2_6_3_1_5396 2
  54 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 275 (accept_3_2 1 54 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 275))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 275 (allA_succ_of_accept 52 53 275 (accept_3_2 52 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 53 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 275 (accept_3_2 49 53 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 275 (accept_3_2 46 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 275 (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 275 (Polychromatic418967fa.accept_14_2_11_9_1_2925 44 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 275 (accept_3_2 43 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 275 (accept_3_2 40 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 275 (accept_3_2 37 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 275 (Polychromatic418967fa.accept_22_14_9_11_1_16907 36 53 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 275
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 275 (accept_3_2 34 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 275 (accept_3_2 31 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 275 (accept_3_2 28 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 275 (accept_3_2 25 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 275
  (Polychromatic418967fa.accept_19_4_15_9_1_8845 23 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 275 (accept_3_2 22 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 275 (accept_3_2 19 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 275
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 275 (accept_3_2 16 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 275 (accept_3_2 13 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 275 (accept_3_2 10 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 275 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 275 (accept_3_2 7 53 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 275 (accept_3_2 4 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  275 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 275 (accept_3_2 1 53 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 275))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 275 (allA_of_3_0 52 52
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 275 (allA_succ_of_accept 50 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 275 (accept_3_2 49 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 275 (accept_3_2 46 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 275 (accept_3_2 43 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 275 (accept_3_2 40 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 275 (accept_3_2 37 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 275 (accept_3_2 34 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 275 (accept_3_2 31 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 275 (accept_3_2 28 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 275 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 275 (accept_3_2 25 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 275 (accept_3_2 22 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 275 (accept_3_2 19 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 275 (accept_3_2 16 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 275 (Polychromatic418967fa.accept_19_15_13_9_1_7324 15 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 275 (accept_3_2 13 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 275 (accept_3_2 10 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 275 (accept_3_2 7 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 51 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 275 (accept_3_2 4 51 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 275 (accept_3_2 1 51 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  275))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 275 (allA_succ_of_accept 49 50 275 (accept_3_2 49
  50 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 275 (Polychromatic418967fa.accept_16_15_2_3_1_4262 47 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 275 (accept_3_2 46 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 50 275 5 9 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 50 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 50 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 275 (accept_3_2 43 50 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 275 (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 50 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 275 5 8 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 275 (accept_3_2 37 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 275
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 50 275 5 7 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 50 275 (accept_3_2 34 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  50 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 50 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 275 (accept_3_2 31 50 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 275 5 6 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 50 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 275 (accept_3_2 28 50 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 275
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 275 25 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 50
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 275 (accept_3_2 22 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 275 5 4 10 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 275 (accept_3_2 19
  50 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 275
  (Polychromatic418967fa.accept_19_18_12_9_1_7315 18 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 275 (accept_3_2 16 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 275 5 3 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 275 (Polychromatic418967fa.accept_19_14_12_9_1_4587 14 50 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 275 (accept_3_2 13 50 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 275 (Polychromatic418967fa.accept_20_12_10_15_1_9869 12 50
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 275
  (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 275 5 2 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 275 (accept_3_2 7 50 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 275 5 1 10 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 275 (accept_3_2 4 50
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 275 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 275
  (Polychromatic418967fa.accept_19_2_12_9_1_10178 2 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 275 (accept_3_2 1 50 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  275)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 275 (allA_of_3_0 49 49 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 275 (allA_succ_of_accept 47 48 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 275 (accept_3_2 46 48 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 275 (accept_3_2 43 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  48 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 48 275 (Polychromatic418967fa.accept_19_3_10_9_1_7338 41 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 275 (accept_3_2 40 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 275 (accept_3_2 37 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  48 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 48 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 275 (accept_3_2 34 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 275 (accept_3_2 31 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  48 275 (Polychromatic418967fa.accept_20_10_8_15_1_11332 30 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 48 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 275 (accept_3_2 28 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 275 (accept_3_2 25 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  48 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 48 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 275 (accept_3_2 22 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 275 (accept_3_2 19 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  48 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 48 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 275 (accept_3_2 16 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 275
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 275 (accept_3_2 13 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  48 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 48 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 275 (accept_3_2 10 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 275 (accept_3_2 7 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48
  275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 48 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 275 (accept_3_2 4 48 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 48
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 275 (accept_3_2 1 48 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 275)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 275 (allA_succ_of_accept 46 47 275 (accept_3_2 46 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 47 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 275 (accept_3_2 43 47 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42
  47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 275 (accept_3_2 40 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 275 (accept_3_2 37 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 275 (accept_3_2 34 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 275 (accept_3_2 31 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 275
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 275 (accept_3_2 28 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 275 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 275 (accept_3_2 25 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 275 (accept_3_2 22 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 275 (accept_3_2 19 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 275 (accept_3_2 16 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 275 (accept_3_2 13 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 275 (accept_3_2 10 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 275 (Polychromatic418967fa.accept_22_9_3_11_1_15411 9 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 275 (accept_3_2 7 47 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 275
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 275 (accept_3_2 4 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 47 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 275 (accept_3_2 1 47 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 275))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 275 (allA_of_3_0 46 46 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 275 (allA_succ_of_accept 44 45 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 275 (accept_3_2 43 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 275 5 8 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 275 (Polychromatic418967fa.accept_12_3_9_11_1_231
  39 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 275 (accept_3_2 37 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 45 275 5 7 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 45 275 (accept_3_2 34 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 275 (accept_3_2 31 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 275 5 6 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 275 (accept_3_2 28 45
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 275 5 5 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 275 (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 275
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 275 (accept_3_2 22 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 275 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 45 275 5 4 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 45 275 (accept_3_2 19 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 275 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 275 (accept_3_2 16 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 275 5 3 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 275 (accept_3_2 13 45
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 275 (Polychromatic418967fa.accept_19_11_7_9_1_8873 11 45 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 275 5 2 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 45 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 275 (accept_3_2 7 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 275 5 1 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 275 (accept_3_2 4 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45
  275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 45 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 275 (accept_3_2 1 45 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 45 275))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 275
  (allA_succ_of_accept 43 44 275 (accept_3_2 43 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  44 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 275 (accept_3_2 40 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 275 (accept_3_2 37 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 275 (accept_3_2 34 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 44 275 11 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 44 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 275 (accept_3_2 31 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 275 (accept_3_2 28 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 275 (accept_3_2 25 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 275 11 2 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 44 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 275 (accept_3_2 19 44 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092
  18 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 275
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 275 (accept_3_2 16 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 275 (accept_3_2 13 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 44 275 11 1 4 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 44 275 (accept_3_2 10 44 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 275 (accept_3_2 7 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 275 (Polychromatic418967fa.accept_20_5_4_15_1_3931 5 44 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 275 (accept_3_2 4 44 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  44 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 275 (accept_3_2 1 44 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 275)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  275 (allA_of_3_0 43 43 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 275 (allA_succ_of_accept 41 42 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 275 (accept_3_2 40 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 275 (accept_3_2 37 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 275 (accept_3_2 34 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 275 (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 275 (accept_3_2 31 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 275 (accept_3_2 28 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 275 (accept_3_2 25 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 275 (accept_3_2 22 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 275 (accept_3_2 19 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 275 (accept_3_2 16 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 275 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 275 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 275 (accept_3_2 13 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 275 (accept_3_2 10 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 275 (accept_3_2 7 42 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 42 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 275 (accept_3_2 4 42 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 275 (accept_3_2 1 42 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  275)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 275 (allA_succ_of_accept 40 41 275 (accept_3_2 40 41 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 275 (accept_3_2 37 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 275 (Polychromatic418967fa.accept_21_14_20_2_1_16906 35 41 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 275 (accept_3_2 34 41 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 275 (Polychromatic418967fa.accept_17_16_7_3_1_4644 33 41
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 275 (accept_3_2 31 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 275 (accept_3_2 28 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 275 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 41 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 275 (accept_3_2 25 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 275 (accept_3_2 22 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 41 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 275
  (Polychromatic418967fa.accept_22_20_19_11_1_12228 20 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 41 275 (accept_3_2 19 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 41 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 275 (accept_3_2 16 41 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 275 (accept_3_2 13 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 275 (Polychromatic418967fa.accept_16_12_9_3_1_5363 12 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 275 (accept_3_2 10 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 275 (accept_3_2 7 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 275 (Polychromatic418967fa.accept_20_5_1_15_1_3928 5 41 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 275 (accept_3_2 4 41 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 275 (accept_3_2 1 41 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 275))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 275
  (allA_of_3_0 40 40 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 275 (allA_succ_of_accept 38 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 275 (accept_3_2 37 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 275 (accept_3_2 34 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 275 (accept_3_2 31 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 275 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 275 (accept_3_2 28 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 275 (accept_3_2 25 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 275 (Polychromatic418967fa.accept_17_6_5_3_1_7134 23 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 275 (accept_3_2 22 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 275 (accept_3_2 19 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 275 (accept_3_2 16 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 275 (accept_3_2 13 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 275 (accept_3_2 10 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 275 (accept_3_2 7 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 275 (accept_3_2 4 39 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 39 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 275 (accept_3_2 1 39 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 275))))))))))))))))))))))))))))))))))))))) (allB_succ 38 275
  (allA_succ_of_accept 37 38 275 (accept_3_2 37 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 275 (accept_3_2 34 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 275 (accept_3_2 31 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 275 (accept_3_2 28 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 275 (accept_3_2 25 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 275 (accept_3_2 22 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 275 (accept_3_2 19 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 275 (accept_3_2 16 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 275
  (Polychromatic418967fa.accept_13_1_12_2_1_384 14 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 275 (accept_3_2 13 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 275 (accept_3_2 10 38 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 275 (accept_3_2 7 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 275 (accept_3_2 4 38 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  38 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 275 (accept_3_2 1 38 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 275)))))))))))))))))))))))))))))))))))))) (allB_succ 37 275
  (allA_of_3_0 37 37 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 275 (allA_succ_of_accept 35 36 275
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 275 (accept_3_2 34 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 275 (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 275 (accept_3_2 31 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 275 (Polychromatic418967fa.accept_19_11_17_9_1_10138 30 36
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 275
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 275 (accept_3_2 28 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 275 (accept_3_2 25 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 275 (accept_3_2 22 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 275 (accept_3_2 19 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 275 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 275 (accept_3_2 16 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 275 (accept_3_2 13 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 275 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 275
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 275 (accept_3_2 10 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 275 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 275 (accept_3_2 7 36 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 275
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 275 (accept_3_2 4 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 275 (Polychromatic418967fa.accept_19_2_17_9_1_10317 2 36 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 275 (accept_3_2 1 36 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 275)))))))))))))))))))))))))))))))))))) (allB_succ 35 275 (allA_succ_of_accept 34 35 275
  (accept_3_2 34 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 275
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 32 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 275 (accept_3_2 31 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 275 5 6 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 275 (accept_3_2 28 35 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 35 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 275
  (Polychromatic418967fa.accept_14_12_7_9_1_726 26 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 275 5 5 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 275 (Polychromatic418967fa.accept_17_6_1_3_1_8503 23 35 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 275 (accept_3_2 22 35 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 275 5 4 7 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 275 (accept_3_2 19
  35 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 275 (Polychromatic418967fa.accept_21_17_14_2_1_4762 17 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 275 (accept_3_2 16 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 275 5 3 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 35 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 275 (accept_3_2 13 35 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 275 5 2 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 275 (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 35 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 275 (Polychromatic418967fa.accept_18_8_17_5_1_9273 8 35 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 275 (accept_3_2 7 35 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 275 5 1 7 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 275 (accept_3_2 4 35
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 275 (Polychromatic418967fa.accept_9_3_8_5_1_65
  3 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 275 (accept_3_2 1 35 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  275))))))))))))))))))))))))))))))))))) (allB_succ 34 275 (allA_of_3_0 34 34 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 275 (allA_succ_of_accept 32 33 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 275 (accept_3_2 31 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 275 (accept_3_2 28 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 275 (accept_3_2 25 33 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 275
  (Polychromatic418967fa.accept_15_8_3_5_1_608 23 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 33 275 11 2 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 33 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 275 (accept_3_2 19 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 275 (accept_3_2 16 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 275 (accept_3_2 13 33 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 33 275 11 1 3 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 275 (accept_3_2 10 33 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 275 (accept_3_2 7 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 33 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 275 (accept_3_2 4 33 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 275 (accept_3_2 1 33 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 275))))))))))))))))))))))))))))))))) (allB_succ 32 275
  (allA_succ_of_accept 31 32 275 (accept_3_2 31 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 275 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 275 (accept_3_2 28 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 275 (accept_3_2 25 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 275 (Polychromatic418967fa.accept_19_5_13_9_1_5957 24 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 32 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 275 (accept_3_2 22 32 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 275 (accept_3_2 19 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 32 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 275 (accept_3_2 16 32 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 275 (accept_3_2 13 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 275 (accept_3_2 10 32 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 275
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 275 (accept_3_2 7 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 275 (accept_3_2 4 32 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  32 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 275 (accept_3_2 1 32 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 275)))))))))))))))))))))))))))))))) (allB_succ 31 275
  (allA_of_3_0 31 31 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 275 (allA_succ_of_accept 29 30 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 275 (accept_3_2 28 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 275 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 275 5 5 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24
  30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 275
  (Polychromatic418967fa.accept_20_3_10_15_1_620 23 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 275 (accept_3_2 22 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 30 275 5 4 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 275 (accept_3_2 19 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 30 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 30 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 275 (accept_3_2 16 30 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 275 5 3 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 275 (Polychromatic418967fa.accept_19_14_11_9_1_3330
  14 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 275 (accept_3_2 13
  30 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 275
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 275 5 2 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 275 (accept_3_2 7 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30
  275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 275 5 1 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 275 (accept_3_2 4 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  275 (Polychromatic418967fa.accept_19_3_11_9_1_10217 3 30 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 30 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 275 (accept_3_2 1 30 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 275)))))))))))))))))))))))))))))) (allB_succ 29 275 (allA_succ_of_accept 28 29 275
  (accept_3_2 28 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 275 (accept_3_2 25 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728
  23 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 275 (accept_3_2 22
  29 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 275 (accept_3_2 19 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 275 (accept_3_2 16 29
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 275 (accept_3_2 13 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 11
  29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 275 (accept_3_2 10 29
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 275
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 275 (accept_3_2 7 29 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5
  29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 275 (accept_3_2 4 29 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 275 (accept_3_2 1 29 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  275))))))))))))))))))))))))))))) (allB_succ 28 275 (allA_of_3_0 28 28 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 275 (allA_succ_of_accept 26 27 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 275 (accept_3_2 25 27 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 275 (accept_3_2 22 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 275 (accept_3_2 19 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 275 (accept_3_2 16 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 275 (accept_3_2 13 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 275 (accept_3_2 10 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 275 (accept_3_2 7 27 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 275 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 27 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 275
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 275 (accept_3_2 4 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 275 (accept_3_2 1 27 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 275))))))))))))))))))))))))))) (allB_succ 26 275 (allA_succ_of_accept 25 26 275 (accept_3_2
  25 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 275 (accept_3_2 22 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 275 (accept_3_2 19 26
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 275 (accept_3_2 16 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 275 (accept_3_2 13 26
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 275 (Polychromatic418967fa.accept_9_3_8_5_1_65
  12 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 275 (accept_3_2 10 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 275 (accept_3_2 7 26 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 26 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 275 (accept_3_2 4 26 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 275 (accept_3_2 1 26 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  275)))))))))))))))))))))))))) (allB_succ 25 275 (allA_of_3_0 25 25 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 275 (allA_succ_of_accept 23 24 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 24 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 275 (accept_3_2 22 24 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 275 (accept_3_2 19 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 275 (accept_3_2 16 24 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 275 (accept_3_2 13 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 275 (accept_3_2 10 24 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 275 (accept_3_2 7 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 275 (accept_3_2 4 24 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  24 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 275 (accept_3_2 1 24 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 275)))))))))))))))))))))))) (allB_succ 23 275
  (allA_succ_of_accept 22 23 275 (accept_3_2 22 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  23 275 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 275 (accept_3_2 19 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 23 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 275
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 275 (accept_3_2 16 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 275 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 275 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 23 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 275 (accept_3_2 13 23 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 275
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 275 (accept_3_2 10 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 275 (Polychromatic418967fa.accept_16_9_7_3_1_614 9 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 275 (accept_3_2 7 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 275 (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 23 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 275
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 275 (accept_3_2 4 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  275 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 23 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 275 (accept_3_2 1 23 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 275))))))))))))))))))))))) (allB_succ 22 275 (allA_of_3_0 22 22 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 21 275 (allA_succ_of_accept 20 21 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 275 (accept_3_2 19 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 275 (accept_3_2 16 21 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 275 (accept_3_2 13 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 275 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 275 (accept_3_2 10 21 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 275 (accept_3_2 7 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 21 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 275 (accept_3_2 4 21 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 275 (accept_3_2 1 21 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 275))))))))))))))))))))) (allB_succ 20 275 (allA_succ_of_accept
  19 20 275 (accept_3_2 19 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 275 (accept_3_2 16 20 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 275 5 3 4 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 20 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 275 (accept_3_2 13 20 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 275 5 2 4 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 275 (accept_3_2 7 20 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 275 5 1 4 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 275 (accept_3_2 4 20
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 275 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 275 (accept_3_2 1 20 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  275)))))))))))))))))))) (allB_succ 19 275 (allA_of_3_0 19 19 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 275 (allA_succ_of_accept 17 18 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 275 (accept_3_2 16 18 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 275 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 18 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 275
  (Polychromatic418967fa.accept_23_14_18_22_1_16905 14 18 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 275 (accept_3_2 13 18 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 18 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 18 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 275 (Polychromatic418967fa.accept_27_11_18_5_1_11244 11 18
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 275 (accept_3_2 10 18 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 275
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 18 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 275 (accept_3_2 7 18 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 275 (accept_3_2 4 18 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 18 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  18 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 275 (accept_3_2 1 18 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 275)))))))))))))))))) (allB_succ 17 275 (allA_succ_of_accept 16
  17 275 (accept_3_2 16 17 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 275 (accept_3_2 13 17 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 275 (accept_3_2 10 17
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 275
  (Polychromatic418967fa.accept_21_9_17_2_1_9537 9 17 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 275 (accept_3_2 7 17 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5
  17 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 275 (accept_3_2 4 17 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 275 (accept_3_2 1 17 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  275))))))))))))))))) (allB_succ 16 275 (allA_of_3_0 16 16 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  275 (allA_succ_of_accept 14 15 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 275 (accept_3_2 13 15 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  15 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 275 5 2 3 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 275
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 275 (accept_3_2 7 15 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 275 5 1 3 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 275 (accept_3_2 4 15 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 275 (accept_3_2 1 15 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  275))))))))))))))) (allB_succ 14 275 (allA_succ_of_accept 13 14 275 (accept_3_2 13 14 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 275 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 14 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  11 14 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 275 (accept_3_2 10
  14 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 14 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 275 (accept_3_2 7 14 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 275 (accept_3_2 4 14 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 14 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 275 (accept_3_2 1 14 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  275)))))))))))))) (allB_succ 13 275 (allA_of_3_0 13 13 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 275
  (allA_succ_of_accept 11 12 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 275 (accept_3_2 10 12 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 12 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 8
  12 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 275 (accept_3_2 7 12 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6
  12 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 275
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 12 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 275 (accept_3_2 4 12 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 275 (accept_3_2 1 12 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 275)))))))))))) (allB_succ 11 275 (allA_succ_of_accept 10 11 275 (accept_3_2 10 11 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  11 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 275 (accept_3_2 7 11 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 11 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 275 (accept_3_2 4 11 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 11 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 275 (Polychromatic418967fa.accept_14_2_11_9_1_2925
  2 11 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 275 (accept_3_2 1 11
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 275))))))))))) (allB_succ 10 275 (allA_of_3_0 10 10 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 275 (allA_succ_of_accept 8 9 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 275 (accept_3_2 7 9 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 9 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 275 (accept_3_2 4 9 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 275 (accept_3_2 1 9 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 275))))))))) (allB_succ 8 275 (allA_succ_of_accept 7 8 275
  (accept_3_2 7 8 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 275 (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 8 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 275 (accept_3_2 4 8 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 275 (accept_3_2 1 8 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 275)))))))) (allB_succ 7 275 (allA_of_3_0 7 7 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 275 (allA_succ_of_accept 5 6 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 275 (accept_3_2 4 6 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 6 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 275 (accept_3_2 1 6 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 275)))))) (allB_succ 5 275 (allA_succ_of_accept 4 5 275 (accept_3_2 4 5 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 275 (accept_3_2 1 5 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 275)))))
  (allB_succ 4 275 (allA_of_3_0 4 4 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 275 (allA_succ_of_accept 2
  3 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 275 (accept_3_2 1 3 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 275)))
  (allB_succ 2 275 (allA_succ_of_accept 1 2 275 (accept_3_2 1 2 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  275)) (allB_two
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


