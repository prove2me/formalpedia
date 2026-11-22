-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch288_Segment001
-- name    : Polychromatic418967fa_Branch288_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:58:46.161885+00:00
-- url     : https://prove2.me/theorems/d6aaddf3-9f4a-44dc-ba69-9ced2969ec9a
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch288_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_288_segment_001 : allB 141 288 :=
  allB_succ 140 288 (allA_succ_of_accept 139 140 288 (accept_3_4 139 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 140 288 2 69 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 140 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 137 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 140 288 4 34 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 140 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 135 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 140 288 2 67 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 140 288 (accept_3_4 133 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 140 288 4 33 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 140 288 (Polychromatic418967fa.accept_21_5_14_15_1_7290 131 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 140 288 2 65 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 140 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 129 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 128 140 288 4 32 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 127 140 288 (accept_3_4 127 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 140 288 2 63 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 140 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 125 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 140 288 4 31 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 140 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 123 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 140 288 2 61 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 140 288 (accept_3_4 121 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 140 288 4 30 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 140 288 (Polychromatic418967fa.accept_19_5_7_3_1_6990 119 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 140 288 2 59 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 140 288
  (Polychromatic418967fa.accept_17_15_4_16_1_6890 117 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 140 288 4 29 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 140 288 (accept_3_4 115 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 140 288 2 57 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 140 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 113 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 140 288 4 28 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 140 288
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 111 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 140 288 2 55 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 140 288 (accept_3_4 109 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 140 288 4 27 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 140 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 107 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 140 288 2 53 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 140 288
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 105 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 140 288 4 26 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 140 288 (accept_3_4 103 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 140 288 2 51 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 140 288 (Polychromatic418967fa.accept_19_6_7_3_1_1733 101 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 288 4 25 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 99 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 140 288 2 49 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 140 288 (accept_3_4 97 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 288 4 24 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 288 (Polychromatic418967fa.accept_25_20_15_13_1_17767 95 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 288 2 47 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 93 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 288 4 23 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 288 (accept_3_4 91 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 288 2 45 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 89 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 288 4 22 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 288
  (Polychromatic418967fa.accept_21_3_14_15_1_10526 87 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 140 288 2 43 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 140 288 (accept_3_4 85 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 288 4 21 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 83 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 288 2 41 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 81 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 288 4 20 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 288 (accept_3_4 79 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 288 2 39 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 288 4 19 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 288
  (Polychromatic418967fa.accept_21_12_14_15_1_8909 75 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 140 288 2 37 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 140 288 (accept_3_4 73 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 288 4 18 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 140 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 288 2 35 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 69 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 288 4 17 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 288 (accept_3_4 67 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 288 2 33 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 288 (Polychromatic418967fa.accept_22_21_8_2_1_16285 65 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 288 4 16 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 288 2 31 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 288 (accept_3_4 61 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 288 4 15 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 288 (Polychromatic418967fa.accept_21_17_14_15_1_5750 59 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 288 2 29 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 57 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 288 4 14 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 288 (accept_3_4 55 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 288 2 27 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 53 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 288 4 13 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 140 288 2 25 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 140 288 (accept_3_4 49 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 288 4 12 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 288 2 23 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 288 4 11 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 288 (accept_3_4 43 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 288 2 21 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 288 (Polychromatic418967fa.accept_21_20_14_15_1_13468 41 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 288 4 10 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 39 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 288 2 19 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 288 (accept_3_4 37 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 288 4 9 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 288 (Polychromatic418967fa.accept_22_13_8_2_1_8451 35 140 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 288 2 17 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491
  33 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 288 4 8 35 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 288
  (accept_3_4 31 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 288 2 15 70 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 288 4 7 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 140 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 288 2 13 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 288 (accept_3_4 25 140 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 288 4 6 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 140
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 288 2 11 70 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 288 4 5 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 288 (accept_3_4 19 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 288 2 9 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 288 (Polychromatic418967fa.accept_15_2_5_3_1_552 17 140 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 288 4 4 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 288
  (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 140 288 2 7 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 140 288 (accept_3_4 13 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 288 4 3 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 140 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 140 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 288 2 5 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 9 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 288 4 2 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 288 (accept_3_4 7 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  288 2 3 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 140 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 288 4 1 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 140 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 140 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 288 2 1 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 288 (accept_3_4 1 140 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 140
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 139 288 (allA_succ_of_accept 138 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 138 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 139 288 (accept_3_5 137 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 139 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 136 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 139 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 135 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 139 288 (accept_3_5 134 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 139 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 133 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 139 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 132 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 139 288 (accept_3_5 131 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 139 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 130 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 139 288
  (Polychromatic418967fa.accept_20_9_19_8_1_1151 129 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 139 288 (accept_3_5 128 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 139 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 127 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 139 288
  (Polychromatic418967fa.accept_17_7_3_16_1_2208 126 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 139 288 (accept_3_5 125 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 124 139 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 139 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 123 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 139 288 (accept_3_5 122 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 139 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 121 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 139 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 120 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 139 288 (accept_3_5 119 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 118 139 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 118 139 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 139 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 117 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 139 288 (accept_3_5 116 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 139 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 115 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 114 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 139 288 (accept_3_5 113 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 139 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 112 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 139 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 111 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 139 288 (accept_3_5 110 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 139 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 109 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 139 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 108 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 139 288 (accept_3_5 107 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 139 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 106 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 105 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 288 (accept_3_5 104 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 139 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 102 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 288 (accept_3_5 101 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 100 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 288
  (Polychromatic418967fa.accept_19_4_6_3_1_15078 99 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 288 (accept_3_5 98 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 97 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 288 (accept_3_5 95 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 94 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 288 (accept_3_5 92 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 91 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 288 (Polychromatic418967fa.accept_21_6_13_15_1_11870 90 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 288 (accept_3_5 89 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 288 (Polychromatic418967fa.accept_27_7_4_18_1_17680 88 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 87 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 288 (accept_3_5 86 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 85 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 288 (accept_3_5 83 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 139 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 81 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 288 (accept_3_5 80 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 288 (Polychromatic418967fa.accept_19_2_6_3_1_4182 78 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 288 (accept_3_5 77 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 76 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 288 (accept_3_5 74 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 288 (Polychromatic418967fa.accept_19_16_6_3_1_6972 73 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 288 (accept_3_5 71 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 70 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 288
  (Polychromatic418967fa.accept_20_9_19_8_1_1151 69 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 288 (accept_3_5 68 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 66 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 288 (accept_3_5 65 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 288
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 288 (accept_3_5 62 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 288 (Polychromatic418967fa.accept_21_18_13_15_1_2884 60 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 288 (accept_3_5 59 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 139 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 288 (accept_3_5 56 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 288 (accept_3_5 53 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 288 (accept_3_5 50 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 49 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 288 (Polychromatic418967fa.accept_21_6_13_15_1_11870 48 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 288 (accept_3_5 47 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 46 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 45 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 288 (accept_3_5 44 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 288 (Polychromatic418967fa.accept_19_5_6_3_1_5578 43 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 288 (accept_3_5 41 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 139 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 288
  (Polychromatic418967fa.accept_19_1_6_3_1_6968 39 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 288 (accept_3_5 38 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 288 (Polychromatic418967fa.accept_19_17_6_3_1_9830 36 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 288 (accept_3_5 35 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 288 (accept_3_5 32 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 288 (accept_3_5 29 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 288 (Polychromatic418967fa.accept_19_9_6_3_1_5563 28 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 288 (accept_3_5 26 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 288 (Polychromatic418967fa.accept_27_25_4_18_1_17766 25 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 288 (accept_3_5 23 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 139
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 288 (accept_3_5 20 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 288 (accept_3_5 17 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 288
  (Polychromatic418967fa.accept_22_15_7_2_1_11694 15 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 139 288 (accept_3_5 14 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 139 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 288 (Polychromatic418967fa.accept_7_5_6_1_1_407
  12 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 288 (accept_3_5 11
  139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 288
  (Polychromatic418967fa.accept_25_10_14_13_1_12587 10 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 288 (accept_3_5 8 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 6 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 288 (accept_3_5 5 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 139 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 288 (accept_3_5 2 139 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 139 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 138 288 (allA_succ_of_accept 137 138 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 137 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 138 288 2 68 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 135 138 288 3 45 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 134 138 288 2 67 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 138 288
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 133 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 132 138 288 6 22 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 131 138 288 (Polychromatic418967fa.accept_19_17_5_3_1_5455 131 138 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 138 288 2 65 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 129 138 288 3 43 46 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 128 138 288 2 64 69
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 138 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 127 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 138 288 6 21 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 138 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 125 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 138 288 2 62 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 123 138 288 3 41 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 122 138 288 2 61 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 138 288
  (Polychromatic418967fa.accept_19_7_5_3_1_13861 121 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 138 288 6 20 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 138 288 (Polychromatic418967fa.accept_21_14_12_15_1_7299 119 138 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 138 288 2 59 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 138 288 3 39 46 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 138 288 2 58 69
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 138 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 138 288 6 19 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 138 288 (Polychromatic418967fa.accept_20_13_18_8_1_4936 113 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 138 288 2 56 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 138 288 3 37 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 138 288 2 55 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 138 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 288 6 18 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 288 (Polychromatic418967fa.accept_17_5_2_16_1_1294 107 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 138 288 2 53 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 138 288 3 35 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 138 288 2 52 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 103 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 288 6 17 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 288 2 50 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 138 288 3 33 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 138 288 2 49 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 288 6 16 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 288 2 47 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 138 288 3 31 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 138 288 2 46 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 288
  (Polychromatic418967fa.accept_20_11_18_8_1_4821 91 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 138 288 6 15 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 138 288 (Polychromatic418967fa.accept_21_5_12_15_1_11875 89 138 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 288 2 44 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 138 288 3 29 46 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 138 288 2 43 69
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 85 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 288 6 14 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 288 2 41 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 138 288 3 27 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 138 288 2 40 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 288
  (Polychromatic418967fa.accept_31_17_14_9_1_17765 79 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 138 288 6 13 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 138 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 77 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 288 2 38 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 138 288 3 25 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 138 288 2 37 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 288 6 12 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 288 2 35 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 138 288 3 23 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 138 288 2 34 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 288 6 11 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 288 (Polychromatic418967fa.accept_17_14_2_16_1_4380 65 138 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 288 2 32 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 138 288 3 21 46 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 138 288 2 31 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 288
  (Polychromatic418967fa.accept_20_1_18_8_1_6359 61 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 288 6 10 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 288 2 29 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 138 288 3 19 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 138 288 2 28 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 288 6 9 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 138 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 288 2 26 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 138 288 3 17 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 288 2 25 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 288 6 8 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 138 288 (Polychromatic418967fa.accept_21_5_12_15_1_11875 47 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 288 2 23 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 288 3 15 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 288 2 22 69 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 288
  (Polychromatic418967fa.accept_20_3_18_8_1_4859 43 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 288 6 7 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 288 2 20 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 288 3 13 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 288 2 19 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 288 6 6 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 288 (Polychromatic418967fa.accept_17_1_2_16_1_5596 35 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 288 2 17 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 288 3 11 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 288 2 16 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 288 6 5 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 288 (Polychromatic418967fa.accept_19_10_5_3_1_13818 29 138 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 288 2 14 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 288 3 9 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 288 2 13 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 288 6 4 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 288 2 11 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 288 3 7 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 288 2 10 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 288
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 288 6 3 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 288 2 8 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 288 3 5 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 288 2 7 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 288 6 2 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 288 2 5 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 288 3 3 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 288 2 4 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7
  138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 288 6 1 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 288
  (Polychromatic418967fa.accept_17_5_2_16_1_1294 5 138 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 288 2 2 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 138 288 3 1 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 138 288 2 1 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 288 (Polychromatic418967fa.accept_17_1_2_16_1_5596 1 138 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 288 (allA_succ_of_accept 136 137 288 (accept_3_4 136 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 137 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 135 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 137 288
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 134 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 137 288 (accept_3_4 133 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 137 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 132 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  131 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 137 288 (accept_3_4
  130 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 137 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 129 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 137 288 (Polychromatic418967fa.accept_22_18_5_2_1_3611 128 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 137 288 (accept_3_4 127 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 137 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 126 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 137 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 125 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 137 288 (accept_3_4 124 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 137 288 (Polychromatic418967fa.accept_22_13_5_2_1_17764 123 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 122 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 122 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 137 288 (accept_3_4 121 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 137 288 (Polychromatic418967fa.accept_19_6_4_3_1_11188 120
  137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 137 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 119 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 137 288 (accept_3_4 118 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 117 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 137 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 116 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 137 288 (accept_3_4 115 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 137 288 (Polychromatic418967fa.accept_17_12_1_16_1_4360 114
  137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 137 288
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 113 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 137 288 (accept_3_4 112 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 137 288 (Polychromatic418967fa.accept_19_16_4_3_1_2946 111 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 110 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 137 288 (accept_3_4 109 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 107 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 137 288 (accept_3_4 106 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 137 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 137 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 104 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 288 (accept_3_4 103 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 102
  137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 137 288 (accept_3_4 100 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 137 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 137 288 (Polychromatic418967fa.accept_22_10_5_2_1_16254 98 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 288 (accept_3_4 97 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 95 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 288 (accept_3_4 94 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 288 (Polychromatic418967fa.accept_21_9_11_15_1_1600 93 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 288 (Polychromatic418967fa.accept_19_16_4_3_1_2946 92 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 288 (accept_3_4 91 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 90 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 288 (accept_3_4 88 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 86 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 288 (accept_3_4 85 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 288 (Polychromatic418967fa.accept_19_8_4_3_1_5559 84 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 83 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 288 (accept_3_4 82 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 288 (Polychromatic418967fa.accept_29_23_21_27_1_17763 81 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 288 (accept_3_4 79 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 288 (Polychromatic418967fa.accept_22_12_5_2_1_8508 78 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 288
  (Polychromatic418967fa.accept_19_1_4_3_1_8404 77 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 288 (accept_3_4 76 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 74 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 288 (accept_3_4 73 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 288
  (Polychromatic418967fa.accept_20_11_17_8_1_4903 71 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 137 288 (accept_3_4 70 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 137 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 137 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 288 (accept_3_4 67 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 66
  137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 288 (accept_3_4 64 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 288 (Polychromatic418967fa.accept_22_18_5_2_1_3611 62 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 288 (accept_3_4 61 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 288 (accept_3_4 58 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 56 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 288 (accept_3_4 55 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 288
  (Polychromatic418967fa.accept_17_2_1_16_1_6946 53 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 288 (accept_3_4 52 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 288 (Polychromatic418967fa.accept_19_13_4_3_1_2945 51 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 288 (accept_3_4 49 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 288 (accept_3_4 46 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 288 (accept_3_4 43 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 288 (accept_3_4 40 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 288 (accept_3_4 37 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 288 (Polychromatic418967fa.accept_17_2_1_16_1_6946 36 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 288 (accept_3_4 34 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 288 (accept_3_4 31 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 288 (accept_3_4 28 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 288 (accept_3_4 25 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 288
  (Polychromatic418967fa.accept_27_23_2_18_1_17762 23 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 137 288 (accept_3_4 22 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 137 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 137 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 288 (accept_3_4 19 137
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 288 (accept_3_4 16 137 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 137 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 288
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 288 (accept_3_4 13 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 288 (Polychromatic418967fa.accept_19_11_4_3_1_5534 11 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 288 (accept_3_4 10 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 137 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 288 (accept_3_4 7 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 288 (Polychromatic418967fa.accept_19_6_4_3_1_11188 6 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 288 (accept_3_4 4 137 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 288
  (Polychromatic418967fa.accept_17_2_1_16_1_6946 2 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 288 (accept_3_4 1 137 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 136 288 (allA_succ_of_accept 135 136 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 135 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 136 288 2 67 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 136 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 133 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 136 288 4 33 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 136 288 (accept_3_5 131 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 136 288 2 65 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 136 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 129 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 136 288 8 16 17 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 136 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 127 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 136 288 2 63 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 136 288 (accept_3_5 125 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 136 288 4 31 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 136 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 123 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 136 288 2 61 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 136 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 121 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 136 288 8 15 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 136 288 (accept_3_5 119 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 136 288 2 59 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 136 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 117 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 136 288 4 29 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 136 288
  (Polychromatic418967fa.accept_22_5_4_2_1_6803 115 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 136 288 2 57 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 136 288 (accept_3_5 113 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 136 288 8 14 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 136 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 111 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 136 288 2 55 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 136 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 109 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 136 288 4 27 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 136 288 (accept_3_5 107 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 136 288 2 53 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 136 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 105 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 136 288 8 13 17 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 136 288 2 51 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 136 288 (accept_3_5 101 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 288 4 25 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 99 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 288 2 49 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 97 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 288 8 12 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 288 (accept_3_5 95 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 288 2 47 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 288 4 23 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 288
  (Polychromatic418967fa.accept_21_7_10_15_1_8906 91 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 136 288 2 45 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 136 288 (accept_3_5 89 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 288 8 11 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 87 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 288 2 43 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 288
  (Polychromatic418967fa.accept_21_1_10_15_1_2828 85 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 136 288 4 21 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 136 288 (accept_3_5 83 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 288 2 41 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 288 8 10 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 288 2 39 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 288 (accept_3_5 77 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 288 4 19 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 288 2 37 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 73 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 288 8 9 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 136 288 (accept_3_5 71 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  136 288 2 35 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 136 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 69 136 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 288 4 17 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 136 288 2 33 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 136 288 (accept_3_5 65
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 136 288 8 8 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 136 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 136 288 2 31 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 136 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 136 288 4 15 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 136 288 (accept_3_5 59 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 136 288 2 29 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 136 288 (Polychromatic418967fa.accept_22_13_4_2_1_3601
  57 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 288 8 7 17 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 288
  (Polychromatic418967fa.accept_23_9_21_12_1_17761 55 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 136 288 2 27 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 136 288 (accept_3_5 53 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 288 4 13 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 288 2 25 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 288
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 288 8 6 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 136 288 (accept_3_5 47 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  136 288 2 23 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 136 288 (Polychromatic418967fa.accept_21_3_10_15_1_4266 45 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 288 4 11 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 288 2 21 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 288 (accept_3_5 41 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 288 8 5 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 136 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 136 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 288 2 19 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 288 4 9 34 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 288 (accept_3_5 35
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 288 2 17 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 288 8 4 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 136 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 136 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 288 2 15 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 288 (accept_3_5 29 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 288 4 7 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 136 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 288 2 13 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 288 8 3 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 136 288 (accept_3_5 23 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  136 288 2 11 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 136 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 136 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 288 4 5 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 288 2 9 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 288 (accept_3_5 17
  136 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 288 8 2 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 288
  (Polychromatic418967fa.accept_25_15_11_13_1_14227 15 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 288 2 7 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 288 4 3 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 288 (accept_3_5 11 136 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 288 2 5 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 288 8 1 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 288 (Polychromatic418967fa.accept_21_7_10_15_1_8906 7 136 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 288 2 3 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 288 (accept_3_5 5 136 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 288 4 1 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 136 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 288 2 1 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 1 136 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 135 288 (allA_succ_of_accept 134 135 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 134 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 135 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 133 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 135 288 3 44 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 135 288 (Polychromatic418967fa.accept_19_17_2_3_1_4190 131 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 135 288
  (Polychromatic418967fa.accept_19_16_2_3_1_5479 130 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 129 135 288 3 43 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 128 135 288 (Polychromatic418967fa.accept_21_2_9_15_1_5747 128 135 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 135 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 127 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 135 288 9 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 125 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 135 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 124 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 135 288 3 41 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 122 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 121 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 135 288 3 40 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 135 288 (Polychromatic418967fa.accept_19_5_2_3_1_5527 119 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 135 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 118 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 135 288 9 13 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 135 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 116 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 115 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 135 288 3 38 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 135 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 113 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 135 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 112 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 135 288 3 37 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 135 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 110 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 288
  (Polychromatic418967fa.accept_21_4_9_15_1_11925 109 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 135 288 9 12 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 135 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 107 135 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 135 288
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 106 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 135 288 3 35 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 103 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 135 288 3 34 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 100 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 135 288 9 11 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 135 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 98 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  97 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 135 288 3 32 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 135 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 95 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 135 288 3 31 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 135 288 (Polychromatic418967fa.accept_10_2_5_8_1_139
  92 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 288
  (Polychromatic418967fa.accept_21_7_9_15_1_5803 91 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 135 288 9 10 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 135 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 89 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 88 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 135 288 3 29 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 288 (Polychromatic418967fa.accept_21_2_9_15_1_5747 86 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 85 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 135 288 3 28 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 288 (Polychromatic418967fa.accept_10_2_5_8_1_139
  82 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 135 288 9 9 15 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 135 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 135 288 (Polychromatic418967fa.accept_21_16_9_15_1_4265 79 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 135 288 3 26 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 135 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 288 3 25 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185
  74 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 135 288 9 8 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 135 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 71 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 70 135
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 135 288 3 23 45 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 135 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 135 288 3 22 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 135 288 (Polychromatic418967fa.accept_20_5_15_8_1_4930
  65 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 64 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 135 288 9 7 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 135
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 288 3 20 45 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 288 (Polychromatic418967fa.accept_19_1_2_3_1_6995 58 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 288 3 19 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  56 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 135 288 9 6 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 135 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 135 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 288 3 17 45 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 135 288
  (Polychromatic418967fa.accept_19_12_2_3_1_11218 50 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 135 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 288 3 16 45 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 46 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 288 9 5 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 288 (Polychromatic418967fa.accept_19_6_2_3_1_11217
  44 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 288 3 14 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 288
  (Polychromatic418967fa.accept_21_19_9_15_1_4217 40 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 135 288 3 13 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 135 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 288 9 4 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 135 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 135 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 288 3 11 45 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 288 3 10 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475
  29 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 288
  (Polychromatic418967fa.accept_21_7_9_15_1_5803 28 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 288 9 3 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 288 (Polychromatic418967fa.accept_21_5_9_15_1_11924 26 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 135 288 3 8 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 135
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 288 3 7 45 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 288 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 288 9 2 15 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 288 3 5 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 288
  (Polychromatic418967fa.accept_20_14_15_8_1_9380 14 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 135 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 135 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 288 3 4 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 288
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 11 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 288 9 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 288 (Polychromatic418967fa.accept_23_8_20_12_1_17760 8 135
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 288 3 2 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 288 (Polychromatic418967fa.accept_19_5_2_3_1_5527 5 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4 135 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 288 3 1 45 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 135 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 288 (allA_succ_of_accept 133 134 288 (accept_3_4 133 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 134 288 2 66 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 134 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 131 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 134 288 2 65 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 134 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 129 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 134 288 2 64 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 134 288 (accept_3_4 127 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 134 288 2 63 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 134 288 (Polychromatic418967fa.accept_19_11_1_3_1_5555 125 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 134 288 2 62 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 134 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 123 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 134 288 2 61 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 134 288 (accept_3_4 121 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 134 288 2 60 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 134 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 119 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 134 288 2 59 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 134 288
  (Polychromatic418967fa.accept_21_12_8_15_1_8955 117 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 134 288 2 58 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 134 288 (accept_3_4 115 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 134 288 2 57 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 134 288 (Polychromatic418967fa.accept_17_11_15_16_1_4377 113 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 134 288 2 56 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 134 288
  (Polychromatic418967fa.accept_19_16_1_3_1_7007 111 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 134 288 2 55 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 134 288 (accept_3_4 109 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 134 288 2 54 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 134 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 107 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 134 288 2 53 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 134 288
  (Polychromatic418967fa.accept_19_10_1_3_1_12548 105 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 134 288 2 52 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 134 288 (accept_3_4 103 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 134 288 2 51 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 134 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 101 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 288 2 50 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 99 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 134 288 2 49 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 134 288 (accept_3_4 97 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 288 2 48 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 288 (Polychromatic418967fa.accept_20_15_14_8_1_9344 95 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 288 2 47 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 288
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 93 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 288 2 46 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 288 (accept_3_4 91 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 288 2 45 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 89 134 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 288 2 44 67 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 288
  (Polychromatic418967fa.accept_19_11_1_3_1_5555 87 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 288 2 43 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 288 (accept_3_4 85 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 288 2 42 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 83 134 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 288 2 41 67 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 288
  (Polychromatic418967fa.accept_19_5_1_3_1_8421 81 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 288 2 40 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 288 (accept_3_4 79 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 288 2 39 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 288 2 38 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 288
  (Polychromatic418967fa.accept_20_15_14_8_1_9344 75 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 134 288 2 37 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 134 288 (accept_3_4 73 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 288 2 36 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 288 2 35 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 288 2 34 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 288 (accept_3_4 67 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 288 2 33 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 288 (Polychromatic418967fa.accept_17_14_15_16_1_1271 65 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 288 2 32 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 288 2 31 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 288 (accept_3_4 61 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 288 2 30 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 134 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 288 2 29 67 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 57 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 288 2 28 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 288 (accept_3_4 55 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 288 2 27 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 288 (Polychromatic418967fa.accept_20_13_14_8_1_4850 53 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 288 2 26 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 288 2 25 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 288 (accept_3_4 49 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 288 2 24 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 288 2 23 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 288 2 22 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 288 (accept_3_4 43 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 288 2 21 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 288 2 20 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 288 2 19 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 288 (accept_3_4 37 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 288 2 18 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 288 (Polychromatic418967fa.accept_17_1_15_16_1_2202 35 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 288 2 17 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 288
  (Polychromatic418967fa.accept_20_13_14_8_1_4850 33 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 134 288 2 16 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 134 288 (accept_3_4 31 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 288 2 15 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 134 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 288 2 14 67 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 288
  (Polychromatic418967fa.accept_21_6_8_15_1_8903 27 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 288 2 13 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 288 (accept_3_4 25 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 288 2 12 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 288 (Polychromatic418967fa.accept_19_4_1_3_1_15091 23 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 288 2 11 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 288
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 134 288 2 10 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 134 288 (accept_3_4 19 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 288 2 9 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 288 2 8 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 288
  (Polychromatic418967fa.accept_20_15_14_8_1_9344 15 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 134 288 2 7 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 134 288 (accept_3_4 13 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 288 2 6 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 288 2 5 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 288 2 4 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 288 (accept_3_4 7 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  288 2 3 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 134 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 288 2 2 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 288 (Polychromatic418967fa.accept_20_3_14_8_1_12152 3 134 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 288 2 1 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 288 (accept_3_4 1 134 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 133 288 (allA_succ_of_accept 132 133 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 132 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 133 288 (accept_3_5 131 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 133 288 (Polychromatic418967fa.accept_15_10_13_3_1_4816 130
  133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 133 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 129 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 133 288 (accept_3_5 128 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 133 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 127 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 133 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 126 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 133 288 (accept_3_5 125 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 133 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 124 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 133 288 (Polychromatic418967fa.accept_20_3_13_8_1_12215 123 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 133 288 (accept_3_5 122 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 121 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 133 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 120 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 133 288 (accept_3_5 119 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 133 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 118 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 117 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 133 288 (accept_3_5 116 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 115 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 133 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 114 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 133 288 (accept_3_5 113 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 133 288 (Polychromatic418967fa.accept_25_12_8_13_1_17759 112 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  111 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 133 288 (accept_3_5
  110 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 133 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 109 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 288 (Polychromatic418967fa.accept_21_3_7_15_1_4300 108 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 288 (accept_3_5 107 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 106 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 105 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 288 (accept_3_5 104 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 103 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 133 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 102 133 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 288 (accept_3_5 101 133 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 288 (Polychromatic418967fa.accept_13_9_3_2_1_399
  100 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 99 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 288 (accept_3_5 98 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 97 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 96 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 288 (accept_3_5 95 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 288 (Polychromatic418967fa.accept_20_14_13_8_1_4847 94 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 288
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 93 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 133 288 (accept_3_5 92 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 91 133 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 133 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 90 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 288 (accept_3_5 89 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 88 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 133 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 87 133 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 288 (accept_3_5 86 133 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 84 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 288 (accept_3_5 83 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 288 (Polychromatic418967fa.accept_21_19_7_15_1_2848 82 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 81 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 288 (accept_3_5 80 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 288
  (Polychromatic418967fa.accept_20_18_13_8_1_9398 78 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 133 288 (accept_3_5 77 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 133 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 288 (accept_3_5 74 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 288
  (Polychromatic418967fa.accept_21_10_7_15_1_8930 73 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 288 (accept_3_5 71 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 70 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 288 (accept_3_5 68 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 288 (Polychromatic418967fa.accept_25_17_8_13_1_17758 67 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 288 (accept_3_5 65 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 64 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 63 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 288 (accept_3_5 62 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 288 (Polychromatic418967fa.accept_21_18_7_15_1_2877 60 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 288 (accept_3_5 59 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 288 (accept_3_5 56 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 288 (accept_3_5 53 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 288 (Polychromatic418967fa.accept_21_10_7_15_1_8930 52 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 51 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 288 (accept_3_5 50 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 288 (accept_3_5 47 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 288 (accept_3_5 44 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 288 (accept_3_5 41 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 39 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 288 (accept_3_5 38 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 288 (accept_3_5 35 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 288
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 33 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 133 288 (accept_3_5 32 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 133 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 288 (Polychromatic418967fa.accept_21_9_7_15_1_5769 30 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 288 (accept_3_5 29 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 288
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 28 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 288 (accept_3_5 26 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 24 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 288 (accept_3_5 23 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 288 (accept_3_5 20 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 288 (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 288 (accept_3_5 17 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 288 (accept_3_5 14 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 133
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 288 (accept_3_5 11 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 288 (accept_3_5 8 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 288 (Polychromatic418967fa.accept_22_7_1_2_1_17757 7 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 288 (accept_3_5 5 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 288 (Polychromatic418967fa.accept_27_4_25_18_1_14078 4 133 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 288 (accept_3_5 2 133 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 133 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 132 288 (allA_succ_of_accept 131 132 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 131 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 132 288 2 65 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 129 132 288 3 43 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 128 132 288 4 32 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 127 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 132 288 6 21 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 132 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 125 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 132 288 4 31 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 123 132 288 3 41 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 122 132 288 2 61 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 121 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 132 288 12 10 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 132 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 119 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 132 288 2 59 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 132 288 3 39 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 132 288 4 29 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 115 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 132 288 6 19 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 132 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 113 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 132 288 4 28 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 132 288 3 37 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 132 288 2 55 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 288
  (Polychromatic418967fa.accept_19_14_18_3_1_12569 109 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 132 288 12 9 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 132 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 132 288 2 53 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 132 288 3 35 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 132 288 4 26 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 132 288 6 17 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 132 288 (Polychromatic418967fa.accept_19_6_18_3_1_11230 101 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 132 288 4 25 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 132 288 3 33 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 288 2 49 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 97 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 288 12 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 132 288 2 47 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 132 288 3 31 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 132 288 4 23 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 91 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 288 6 15 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 288 4 22 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 132 288 3 29 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 132 288 2 43 66 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 288 12 7 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 83 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 288 2 41 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 132 288 3 27 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 132 288 4 20 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 288 6 13 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 77 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 288 4 19 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 132 288 3 25 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 132 288 2 37 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 73 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 132 288 12 6 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 132 288 (Polychromatic418967fa.accept_17_3_13_16_1_2183 71 132 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 288 2 35 66 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 132 288 3 23 44 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 132 288 4 17 33
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 288 6 11 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 288 4 16 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 132 288 3 21 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 132 288 2 31 66 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 288 12 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 288 (Polychromatic418967fa.accept_19_2_18_3_1_5517 59 132 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 288 2 29 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 132 288 3 19 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 288 4 14 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 288 6 9 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 132 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 53 132 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 288 4 13 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 132 288 3 17 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 288 2 25 66 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 49 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 288 12 4 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 288 2 23 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 132 288 3 15 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 288 4 11 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 132 288 6 7 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 288 (Polychromatic418967fa.accept_21_20_6_15_1_11937 41 132 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 288 4 10 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 288 3 13 44 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 288 2 19 66
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 288 12 3 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 288 2 17 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 288 3 11 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 288 4 8 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 288
  (Polychromatic418967fa.accept_21_10_6_15_1_8929 31 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 132 288 6 5 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 132 288 (Polychromatic418967fa.accept_17_12_13_16_1_3226 29 132 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 288 4 7 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 288 3 9 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 288 2 13 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 288 12 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 288 2 11 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 288 3 7 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 288 4 5 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 288 6 3 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 132 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 288 4 4 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 288 3 5 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 288 2 7 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 132 288 12 1 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 288 (Polychromatic418967fa.accept_19_11_18_3_1_1755 11 132 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 288 2 5 66 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 288 3 3 44 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 288 4 2 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 132 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 288 6 1 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 288 4 1 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 288 3 1 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 288 2 1 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 288 (Polychromatic418967fa.accept_21_1_6_15_1_5742 1 132 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 288 (allA_succ_of_accept 130 131 288 (accept_3_4 130 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 129 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 131 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 128
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 131 288 (accept_3_4 127
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 131 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 126 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 125 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 131 288 (accept_3_4 124 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 123 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 131 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 122 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 131 288 (accept_3_4 121 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 131 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 120 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 131 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 119 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 131 288 (accept_3_4 118 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 131 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 117
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 131 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 116 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 131 288 (accept_3_4 115 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 131 288 (Polychromatic418967fa.accept_21_9_5_15_1_5741 114 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 113 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 131 288 (accept_3_4 112 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416
  111 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 131 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 110 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 131 288 (accept_3_4 109 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 131 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 107 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 288 (accept_3_4 106 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 131 288 (Polychromatic418967fa.accept_30_15_11_18_1_9340 105
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 104 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 131 288 (accept_3_4 103 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 288 (accept_3_4 100 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 99 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 288
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 98 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 288 (accept_3_4 97 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 96 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 288 (accept_3_4 94 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 93 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 288
  (Polychromatic418967fa.accept_19_16_17_3_1_2916 92 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 131 288 (accept_3_4 91 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 89 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 288 (accept_3_4 88 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 131 288 (Polychromatic418967fa.accept_17_1_12_16_1_2211 86 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 288 (accept_3_4 85 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 84 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 288 (accept_3_4 82 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 288 (accept_3_4 79 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 77 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 288 (accept_3_4 76 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 288 (Polychromatic418967fa.accept_21_12_5_15_1_17705 75 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 288 (accept_3_4 73 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 288 (Polychromatic418967fa.accept_19_15_17_3_1_13760 72
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 71 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 288 (accept_3_4 70 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 68 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 288 (accept_3_4 67 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 288
  (Polychromatic418967fa.accept_19_8_17_3_1_4154 65 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 288 (accept_3_4 64 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 288 (accept_3_4 61 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 288 (accept_3_4 58 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 57 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 288 (accept_3_4 55 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 288 (Polychromatic418967fa.accept_19_16_17_3_1_2916 54 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 288 (accept_3_4 52 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 51 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 288 (Polychromatic418967fa.accept_19_12_17_3_1_5515 50 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 288 (accept_3_4 49 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 288
  (Polychromatic418967fa.accept_17_13_12_16_1_6908 47 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 131 288 (accept_3_4 46 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 288 (accept_3_4 43 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 288 (accept_3_4 40 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 288 (accept_3_4 37
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 131 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 288 (accept_3_4 34 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 131 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 288 (accept_3_4 31 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 288 (Polychromatic418967fa.accept_17_13_12_16_1_6908 30 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 288 (accept_3_4 28 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 288
  (Polychromatic418967fa.accept_22_4_21_2_1_3581 26 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 288 (accept_3_4 25 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 288 (accept_3_4 22 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 131
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 288 (accept_3_4 19 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 288 (accept_3_4 16 131 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 288 (Polychromatic418967fa.accept_19_15_17_3_1_13760 15 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 288 (accept_3_4 13 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 131 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 288 (accept_3_4 10 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9
  131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 288
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 288 (accept_3_4 7 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 288 (Polychromatic418967fa.accept_19_5_17_3_1_4152 5 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 288 (accept_3_4 4 131 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 288
  (Polychromatic418967fa.accept_19_2_17_3_1_11224 2 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 288 (accept_3_4 1 131 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 130 288 (allA_succ_of_accept 129 130 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 129 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 130 288 2 64 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 130 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 127 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 130 288 2 63 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 130 288 (accept_3_5 125 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 130 288 2 62 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 130 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 123 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 130 288 2 61 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 130 288
  (Polychromatic418967fa.accept_22_11_20_2_1_3577 121 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 130 288 2 60 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 130 288 (accept_3_5 119 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 130 288 2 59 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 130 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 117 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 130 288 2 58 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 130 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 130 288 2 57 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 130 288 (accept_3_5 113 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 130 288 2 56 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 130 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 111 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 130 288 2 55 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 109 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 288 2 54 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 288 (accept_3_5 107 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 288 2 53 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 130 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 105 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 130 288 2 52 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 130 288 2 51 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 130 288 (accept_3_5 101 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 130 288 2 50 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 130 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 99 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 130 288 2 49 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 130 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 97 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 130 288 2 48 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 130 288 (accept_3_5 95 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 130 288 2 47 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 288 (Polychromatic418967fa.accept_19_17_16_3_1_8401 93 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 288 2 46 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 130 288
  (Polychromatic418967fa.accept_19_15_16_3_1_8409 91 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 130 288 2 45 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 130 288 (accept_3_5 89 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 130 288 2 44 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 288 2 43 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 130 288
  (Polychromatic418967fa.accept_20_5_10_8_1_6397 85 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 130 288 2 42 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 130 288 (accept_3_5 83 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 288 2 41 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 288 2 40 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 288
  (Polychromatic418967fa.accept_27_25_22_18_1_17756 79 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 130 288 2 39 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 130 288 (accept_3_5 77 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 288 2 38 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 288 2 37 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 288 2 36 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 288 (accept_3_5 71 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 288 2 35 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 288 2 34 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 288 2 33 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 288 (accept_3_5 65 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 288 2 32 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 288 (Polychromatic418967fa.accept_17_12_11_16_1_6903 63 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 288 2 31 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 288 2 30 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 288 (accept_3_5 59 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 288 2 29 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 288 (Polychromatic418967fa.accept_20_17_10_8_1_9374 57 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 288 2 28 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 288
  (Polychromatic418967fa.accept_19_17_16_3_1_8401 55 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 130 288 2 27 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 130 288 (accept_3_5 53 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 288 2 26 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 288 2 25 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 288
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 49 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 130 288 2 24 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 130 288 (accept_3_5 47 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 288 2 23 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 288 2 22 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 288
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 130 288 2 21 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 130 288 (accept_3_5 41 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 288 2 20 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 288 2 19 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 288 2 18 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 288 (accept_3_5 35 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 288 2 17 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 288 2 16 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 288 2 15 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 288 (accept_3_5 29 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 288 2 14 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 288 (Polychromatic418967fa.accept_20_7_10_8_1_9411 27 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 288 2 13 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 288 2 12 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 288 (accept_3_5 23 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 288 2 11 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 288 2 10 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 288 2 9 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 288 (accept_3_5 17 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 288 2 8 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 288 2 7 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 288
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 130 288 2 6 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 130 288 (accept_3_5 11 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 288 2 5 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 130 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 288 2 4 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 288 2 3 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 288 (accept_3_5 5 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  288 2 2 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 288 2 1 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 1 130 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 129 288 (allA_succ_of_accept 128 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 128 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 129 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 127 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 129 288 3 42 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 129 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 125 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 124 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 129 288 3 41 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 129 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 122 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 121 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 129 288 3 40 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 129 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 119 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 129 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 118 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 129 288 3 39 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 116 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 288 (Polychromatic418967fa.accept_11_5_8_2_1_588
  115 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 129 288 3 38 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 129 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 113 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 288 (Polychromatic418967fa.accept_19_17_15_3_1_4174 112 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 129 288 3 37 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 110 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 129 288 3 36 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10
  107 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 288
  (Polychromatic418967fa.accept_21_1_3_15_1_5797 106 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 129 288 3 35 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 129 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 104 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 129 288 3 34 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 129 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 101 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 100 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 129 288 3 33 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 129 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 98 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 97 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 129 288 3 32 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 288 (Polychromatic418967fa.accept_10_4_9_8_1_125
  94 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 129 288 3 31 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 129 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 92 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 91 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 129 288 3 30 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 129 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 88 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 129 288 3 29 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 85 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 129 288 3 28 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 129 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 83 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 82 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 129 288 3 27 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 129 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 80 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 79
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 129 288 3 26 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 129 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 288 (Polychromatic418967fa.accept_28_20_17_8_1_17671 76 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 129 288 3 25 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 129 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 129 288 3 24 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 129 288 (Polychromatic418967fa.accept_10_1_9_8_1_123
  71 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 70 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 129 288 3 23 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 129 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 129 288 3 22 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 129 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 288 3 21 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 62 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 129 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 288 3 20 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 288
  (Polychromatic418967fa.accept_20_19_9_8_1_12192 59 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 129 288 3 19 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 129 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 55 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 288 3 18 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 288
  (Polychromatic418967fa.accept_21_10_3_15_1_13463 52 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 129 288 3 17 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 129 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 50 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 288 3 16 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 46
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 288 3 15 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 288 3 14 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 288 (Polychromatic418967fa.accept_10_1_9_8_1_123
  41 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 288 3 13 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 288 3 12 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 288
  (Polychromatic418967fa.accept_15_5_9_3_1_528 35 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 288 3 11 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 31 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 288 3 10 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 129 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 288 3 9 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 288 3 8 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 288 (Polychromatic418967fa.accept_21_1_3_15_1_5797 22 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 288 3 7 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 288 (Polychromatic418967fa.accept_15_5_9_3_1_528
  20 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 288 3 6 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 288 3 5 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 288 3 4 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 129 288 3 3 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 129 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 129 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  7 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 288 3 2 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 288 3 1 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 129 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 288 (allA_succ_of_accept 127 128 288 (accept_3_4 127 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 128 288 2 63 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 128 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 125 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 128 288 4 31 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 128 288
  (Polychromatic418967fa.accept_19_9_14_3_1_2912 123 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 128 288 2 61 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 128 288 (accept_3_4 121 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 128 288 8 15 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 128 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 119 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 128 288 2 59 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 128 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 117 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 128 288 4 29 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 128 288 (accept_3_4 115 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 128 288 2 57 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 128 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 113 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 128 288 16 7 8 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 111 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 128 288 2 55 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 128 288 (accept_3_4 109 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 288 4 27 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 107 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 288 2 53 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 288
  (Polychromatic418967fa.accept_27_24_20_18_1_17755 105 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 128 288 8 13 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 128 288 (accept_3_4 103 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 288 2 51 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 288 4 25 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 99 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 288 2 49 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 288 (accept_3_4 97 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 288 32 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 128 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 95 128 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 288 2 47 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 288 (Polychromatic418967fa.accept_17_8_9_16_1_6844
  93 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 128 288 4 23 32 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 128 288
  (accept_3_4 91 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 128 288 2 45 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 288
  (Polychromatic418967fa.accept_22_1_18_2_1_13248 89 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 128 288 8 11 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 128 288 2 43 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 128 288 (accept_3_4 85 128 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 128 288 4 21 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 128 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 128 288 2 41 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 128 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 81 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 128 288 16 5 8 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 128 288 (accept_3_4 79 128 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 128 288 2 39 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 128 288
  (Polychromatic418967fa.accept_27_23_20_18_1_8273 77 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 128 288 4 19 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 128 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 128 288 2 37 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 128 288 (accept_3_4 73 128 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 128 288 8 9 16 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 128 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 71 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 128 288 2 35 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 128 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 128 288 4 17 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 128 288 (accept_3_4 67 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 128 288 2 33 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 128 288 (Polychromatic418967fa.accept_15_5_8_3_1_556
  65 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 288 32 2 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 288
  (Polychromatic418967fa.accept_27_9_20_18_1_17754 63 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 128 288 2 31 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 128 288 (accept_3_4 61 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 288 4 15 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 288 2 29 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 288 8 7 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 128 288 (accept_3_4 55 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  128 288 2 27 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 128 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 128 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 288 4 13 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 288 (Polychromatic418967fa.accept_21_9_2_15_1_1622
  51 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 128 288 2 25 64 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 128 288
  (accept_3_4 49 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 128 288 16 3 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 128 288
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 47 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 128 288 2 23 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 128 288 4 11 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 128 288 (accept_3_4 43 128 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 128 288 2 21 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 128 288 8 5 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 128 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 128 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 288 2 19 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 288 (accept_3_4 37 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 288 4 9 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 128
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 288 2 17 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 288
  (Polychromatic418967fa.accept_23_10_13_12_1_17722 33 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 128 288 32 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 288 (accept_3_4 31 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 288 2 15 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 128 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 288 4 7 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 288 2 13 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 288 (accept_3_4 25 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 288 8 3 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 288 2 11 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 288
  (Polychromatic418967fa.accept_27_21_20_18_1_17753 21 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 128 288 4 5 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 128 288 (accept_3_4 19 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 288 2 9 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 288 16 1 8 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 15 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 288 2 7 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 288 (accept_3_4 13 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 288 4 3 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 128 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 128 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 288 2 5 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9
  128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 288 8 1 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 288 (accept_3_4 7
  128 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 288 2 3 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 288
  (Polychromatic418967fa.accept_15_5_8_3_1_556 5 128 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 128 288 4 1 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 128 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 288 2 1 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 288 (accept_3_4 1 128 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 288 (allA_succ_of_accept 126 127 288 (Polychromatic418967fa.accept_17_7_8_16_1_6966 126 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 288 (accept_3_5 125 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 127 288 (Polychromatic418967fa.accept_15_4_7_3_1_119
  124 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 123 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 127 288 (accept_3_5 122 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 127 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 121 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 127 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 120 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 127 288 (accept_3_5 119 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 127 288 (Polychromatic418967fa.accept_19_4_13_3_1_5571 118 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 117 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 127 288 (accept_3_5 116 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 127 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 115 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 127 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 114 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 288 (accept_3_5 113 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 127 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 112 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 288
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 111 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 127 288 (accept_3_5 110 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 109 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 288
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 108 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 127 288 (accept_3_5 107 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 127 288 (Polychromatic418967fa.accept_19_11_13_3_1_9820 106 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 288 (accept_3_5 104 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 103 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 102 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 288 (accept_3_5 101 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 100 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 288 (accept_3_5 98 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 97 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 96 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 288 (accept_3_5 95 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 94 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 288
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 93 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 288 (accept_3_5 92 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 91 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 288 (accept_3_5 89 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 288 (Polychromatic418967fa.accept_19_12_13_3_1_5447 88 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 288
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 87 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 288 (accept_3_5 86 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 84 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 288 (accept_3_5 83 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 288 (Polychromatic418967fa.accept_17_14_8_16_1_6863 82 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 81 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 288 (accept_3_5 80 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 79 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 288 (Polychromatic418967fa.accept_27_24_19_18_1_15951 78 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 288 (accept_3_5 77 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 76 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 288 (accept_3_5 74 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 73 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 288 (accept_3_5 71 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 288 (accept_3_5 68 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 288 (Polychromatic418967fa.accept_19_10_13_3_1_13772 67 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 288 (Polychromatic418967fa.accept_19_9_13_3_1_9829 66 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 288 (accept_3_5 65 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 64 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 288 (accept_3_5 62 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 288 (Polychromatic418967fa.accept_19_4_13_3_1_5571 61 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 288 (accept_3_5 59 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 58 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 57 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 288 (accept_3_5 56 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 55 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 288
  (Polychromatic418967fa.accept_19_16_13_3_1_5544 54 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 127 288 (accept_3_5 53 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 127 288 (Polychromatic418967fa.accept_21_10_1_15_1_10541 52 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 127 288 (accept_3_5 50 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 288 (accept_3_5 47 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 288
  (Polychromatic418967fa.accept_19_8_13_3_1_4172 46 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 127 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 288 (accept_3_5 44 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 127 288 (Polychromatic418967fa.accept_17_9_8_16_1_2176 43 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 42 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 288 (accept_3_5 41 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 288 (accept_3_5 38 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 288
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 288 (accept_3_5 35 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 288 (Polychromatic418967fa.accept_21_12_1_15_1_8924 33 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 288 (accept_3_5 32 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 30 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 288 (accept_3_5 29 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 288 (Polychromatic418967fa.accept_19_9_13_3_1_9829 28 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 288 (accept_3_5 26 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 127 288 (accept_3_5 23 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 127 288 (Polychromatic418967fa.accept_25_22_2_13_1_17752 22 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 288 (accept_3_5 20 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 288 (accept_3_5 17 127 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 127
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 288 (accept_3_5 14 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 288 (Polychromatic418967fa.accept_27_13_19_18_1_10368 13 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 288 (accept_3_5 11 127 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 288
  (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 127 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 288 (accept_3_5 8 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 127 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449
  6 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 288 (accept_3_5 5
  127 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 4 127 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 127 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 288 (accept_3_5 2 127 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 127 288 (Polychromatic418967fa.accept_20_1_7_8_1_4877 1 127 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 288 (allA_succ_of_accept 125 126 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 125 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 126 288 2 62 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 123 126 288 3 41 42 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 122 126 288 2 61 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 121 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 126 288 6 20 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 126 288 (Polychromatic418967fa.accept_22_9_16_2_1_8457 119 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 126 288 2 59 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 126 288 9 13 14 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 126 288 2 58 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 288
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 115 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 288 6 19 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 113 126 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 288 2 56 63 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 126 288 3 37 42 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 126 288 2 55 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 109 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 288 18 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 107 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 288 2 53 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 126 288 3 35 42 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 126 288 2 52 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 103 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 288 6 17 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 101 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 288 2 50 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 126 288 9 11 14 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 126 288 2 49 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 97 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 288 6 16 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 95 126 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 288 2 47 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 126 288 3 31 42 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 126 288 2 46 63 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 288 18 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 126 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 89 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 288 2 44 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 126 288 3 29 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 126 288 2 43 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 288 6 14 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 288 2 41 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 126 288 9 9 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 126 288 2 40 63 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 79 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 288 6 13 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 288 (Polychromatic418967fa.accept_22_11_16_2_1_16273 77 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 288 2 38 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 126 288 3 25 42 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 126 288 2 37 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 73 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 288 18 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 126 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 288 2 35 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 126 288 3 23 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 126 288 2 34 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 288
  (Polychromatic418967fa.accept_19_10_12_3_1_12558 67 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 126 288 6 11 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 126 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 288 2 32 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 288 9 7 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 288 2 31 63 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 288 6 10 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 59 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 288 2 29 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 288 3 19 42 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 288 2 28 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 288 18 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 288 2 26 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 288 3 17 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 288 2 25 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 49 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 288 6 8 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 288 (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 126 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 288 2 23 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 288 9 5 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 288 2 22 63 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 288 6 7 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 288 2 20 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 288 3 13 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 288 2 19 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 288
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 37 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 288 18 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 288 2 17 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 288 3 11 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 288 2 16 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 288 6 5 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 288 2 14 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 288 9 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 288 2 13 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 288 6 4 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 288 2 11 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 288 3 7 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 288 2 10 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 288 18 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 288 (Polychromatic418967fa.accept_19_17_12_3_1_12555 17 126 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 288 2 8 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 288 3 5 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 288 2 7 63 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 288 6 2 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 126 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 288 2 5 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 288 9 1 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 288 2 4 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7
  126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 288 6 1 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 126 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 126 288 2 2 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 126 288 3 1 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 126 288 2 1 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 126 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 288 (allA_succ_of_accept 124 125 288 (accept_3_4 124 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 123 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139
  122 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 288 (accept_3_4
  121 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 288
  (Polychromatic418967fa.accept_23_5_10_12_1_14592 120 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 125 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 119 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 125 288 (accept_3_4 118 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 116 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 288 (accept_3_4 115 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 114 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 113 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 288 (accept_3_4 112 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 111 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 110 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 288 (accept_3_4 109 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 108 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 288 (accept_3_4 106 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 105 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 288
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 104 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 125 288 (accept_3_4 103 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 102 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 101
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 288 (accept_3_4 100
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 99 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 98 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 288 (accept_3_4 97 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 288
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 95 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 125 288 (accept_3_4 94 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 92 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 288 (accept_3_4 91 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 288
  (Polychromatic418967fa.accept_19_14_11_3_1_5508 90 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 288 (accept_3_4 88 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 288 (accept_3_4 85 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 288 (accept_3_4 82 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 81 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 288
  (Polychromatic418967fa.accept_19_4_11_3_1_13801 80 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 125 288 (accept_3_4 79 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 125 288 (Polychromatic418967fa.accept_17_10_6_16_1_6862 78 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  77 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 288 (accept_3_4 76
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 125 288 (Polychromatic418967fa.accept_20_14_5_8_1_4870 74 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 288 (accept_3_4 73 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484
  71 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 288 (accept_3_4 70
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 69 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 288 (accept_3_4 67 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 125 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 66 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 288 (accept_3_4 64 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 288 (accept_3_4 61 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280 60 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 288 (accept_3_4 58 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 288 (Polychromatic418967fa.accept_19_18_11_3_1_11183 56 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 288 (accept_3_4 55 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 288 (accept_3_4 52 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 50 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 288 (accept_3_4 49 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 288 (Polychromatic418967fa.accept_19_10_11_3_1_12543 48
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 288 (accept_3_4 46 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 288 (accept_3_4 43 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 41 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 288 (accept_3_4 40 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 288 (accept_3_4 37 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 125
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 288
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 288 (accept_3_4 34 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 288 (accept_3_4 31 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 288
  (Polychromatic418967fa.accept_19_10_11_3_1_12543 29 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 288 (accept_3_4 28 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 288 (accept_3_4 25 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 288 (Polychromatic418967fa.accept_15_9_5_3_1_554
  24 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 288 (accept_3_4 22 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 288 (accept_3_4 19 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 288 (Polychromatic418967fa.accept_19_18_11_3_1_11183 18
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 288 (accept_3_4 16 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 288 (Polychromatic418967fa.accept_20_15_5_8_1_4920 15 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 288 (Polychromatic418967fa.accept_19_14_11_3_1_5508 14 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 288 (accept_3_4 13 125 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 288
  (Polychromatic418967fa.accept_29_11_9_27_1_17751 11 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 125 288 (accept_3_4 10 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 288 (accept_3_4 7 125 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 6
  125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 288 (accept_3_4 4 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 125 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 288 (accept_3_4 1 125 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 288 (allA_succ_of_accept 123 124 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 123 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 124 288 2 61 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 124 288
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 121 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 124 288 4 30 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 124 288 (accept_3_5 119 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 124 288 2 59 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 124 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 117 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 124 288 4 29 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 124 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 124 288 2 57 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 124 288 (accept_3_5 113 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 124 288 4 28 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 124 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 124 288 2 55 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 124 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 124 288 4 27 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 124 288 (accept_3_5 107 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 124 288 2 53 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 124 288 (Polychromatic418967fa.accept_27_24_16_18_1_17714 105 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 124 288 4 26 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 124 288
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 103 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 124 288 2 51 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 124 288 (accept_3_5 101 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 124 288 4 25 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 124 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 99 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 288 2 49 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 124 288 4 24 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 124 288 (accept_3_5 95 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 288 2 47 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 288 (Polychromatic418967fa.accept_21_9_19_15_1_5782 93 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 288 4 23 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 288
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 91 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 288 2 45 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 288 (accept_3_5 89 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 288 4 22 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 288 2 43 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 288
  (Polychromatic418967fa.accept_19_9_10_3_1_1738 85 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 288 4 21 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 288 (accept_3_5 83 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 288 2 41 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 288 4 20 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 288 2 39 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 288 (accept_3_5 77 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 288 4 19 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 75 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 288 2 37 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 288 4 18 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 288 (accept_3_5 71 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 288 2 35 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 288 4 17 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 288 2 33 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 288 (accept_3_5 65 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 288 4 16 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 288 (Polychromatic418967fa.accept_22_19_14_2_1_3635 63 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 288 2 31 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 288
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 61 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 288 4 15 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 288 (accept_3_5 59 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 288 2 29 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 288 4 14 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 288 2 27 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 288 (accept_3_5 53 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 288 4 13 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 288 (Polychromatic418967fa.accept_19_13_10_3_1_11235 51 124 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 288 2 25 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 288 4 12 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 288 (accept_3_5 47 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 288 2 23 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 288 4 11 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 288
  (Polychromatic418967fa.accept_19_5_10_3_1_5460 43 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 288 2 21 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 288 (accept_3_5 41 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 288 4 10 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 288 2 19 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 288 4 9 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 288 (accept_3_5 35 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 288 2 17 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 33 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 288 4 8 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 288 2 15 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 288 (accept_3_5 29 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 288 4 7 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 124 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 124 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 288 2 13 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25
  124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 288 4 6 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 288 (accept_3_5 23
  124 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 288 2 11 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 288 4 5 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 124 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 288 2 9 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 288 (accept_3_5 17 124 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 288 4 4 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 288 (Polychromatic418967fa.accept_19_15_10_3_1_12550 15 124
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 288 2 7 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 288 4 3 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 288 (accept_3_5 11 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 288 2 5 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 124 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 288 4 2 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 124 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 288 2 3 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 288 (accept_3_5 5
  124 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 288 4 1 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 288 2 1 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 124 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 123 288 (allA_succ_of_accept 122 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 122 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 121 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 123 288 3 40 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 123 288 (Polychromatic418967fa.accept_21_14_18_15_1_5756 119 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 118 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 123 288 3 39 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 123 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 116 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 123 288 3 38 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 123 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 113 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 112 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 123 288 3 37 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 110 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 288
  (Polychromatic418967fa.accept_19_14_9_3_1_13821 109 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 123 288 3 36 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 123 288 (Polychromatic418967fa.accept_17_5_4_16_1_6925 107 123 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 106 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 123 288 3 35 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 123 288 (Polychromatic418967fa.accept_21_20_18_15_1_11881 104 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 123 288 3 34 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 100 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 123 288 3 33 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 123 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 98 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 288
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 97 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 123 288 3 32 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 123 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 95 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 94 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 123 288 3 31 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 123 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 92 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  91 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 123 288 3 30 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 123 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 88 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 123 288 3 29 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 123 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  86 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 123 288 3 28 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 123 288 (Polychromatic418967fa.accept_17_15_4_16_1_6890 83 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 82 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 123 288 3 27 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 288 (Polychromatic418967fa.accept_13_1_6_2_1_377
  79 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 123 288 3 26 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 123 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 123 288 3 25 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 123 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200
  74 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 288 3 24 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 288
  (Polychromatic418967fa.accept_19_13_9_3_1_9806 70 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 123 288 3 23 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 288
  (Polychromatic418967fa.accept_19_10_9_3_1_7009 67 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 123 288 3 22 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 123 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 64 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 288 3 21 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 62 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 123 288 3 20 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 288
  (Polychromatic418967fa.accept_20_18_3_8_1_7903 58 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 288 3 19 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 288 3 18 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 53 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52
  123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 288 3 17 41 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 288
  (Polychromatic418967fa.accept_19_12_9_3_1_13858 50 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 123 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 288 3 16 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 288 3 15 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 288 (Polychromatic418967fa.accept_19_6_9_3_1_15079
  44 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 288 3 14 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 123 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  40 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 288 3 13 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 288 (Polychromatic418967fa.accept_17_3_4_16_1_3208 37 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 288 3 12 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  35 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 34 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 288 3 11 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 288 3 10 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 288 (Polychromatic418967fa.accept_19_10_9_3_1_7009 29 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 288
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 28 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 123 288 3 9 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 123 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 288 3 8 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 123
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 288 3 7 41 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 288
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 20 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 288 3 6 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17
  123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 288 3 5 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 288 (Polychromatic418967fa.accept_19_13_9_3_1_9806 13 123
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 288 3 4 41 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 288 3 3 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 123 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 288
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 7 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 288 3 2 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 123 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 288 3 1 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 288
  (Polychromatic418967fa.accept_21_2_18_15_1_4236 2 123 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 123 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 288 (allA_succ_of_accept 121 122 288 (accept_3_4 121 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 288 2 60 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 119 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 288 2 59 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 117 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 288 2 58 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 288 (accept_3_4 115 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 288 2 57 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 113 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 288 2 56 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 111 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 288 2 55 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 288 (accept_3_4 109 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 288 2 54 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 288 2 53 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 105 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 288 2 52 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 288 (accept_3_4 103 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 288 2 51 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 101 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 288 2 50 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 288
  (Polychromatic418967fa.accept_19_4_8_3_1_8416 99 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 288 2 49 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 288 (accept_3_4 97 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 288 2 48 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 288 2 47 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 288 2 46 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 288 (accept_3_4 91 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 288 2 45 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 288 2 44 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 87 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 288 2 43 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 288 (accept_3_4 85 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 288 2 42 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 288 (Polychromatic418967fa.accept_25_8_22_13_1_17750 83 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 288 2 41 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 288 2 40 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 288 (accept_3_4 79 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 288 2 39 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 288 2 38 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 288 2 37 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 288 (accept_3_4 73 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 288 2 36 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 288 (Polychromatic418967fa.accept_19_14_8_3_1_6981 71 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 288 2 35 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 288 2 34 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 288 (accept_3_4 67 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 288 2 33 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 288 2 32 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 288
  (Polychromatic418967fa.accept_19_6_8_3_1_11219 63 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 288 2 31 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 288 (accept_3_4 61 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 288 2 30 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 59 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 288 2 29 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 288 2 28 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 288 (accept_3_4 55 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 288 2 27 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 288 2 26 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 288 2 25 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 288 (accept_3_4 49 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 288 2 24 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 288 2 23 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 288 2 22 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 288 (accept_3_4 43 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 288 2 21 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 288 (Polychromatic418967fa.accept_17_7_3_16_1_2208 41 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 288 2 20 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 288 2 19 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 288 (accept_3_4 37 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 288 2 18 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 288 2 17 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 288 2 16 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 288 (accept_3_4 31 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 288 2 15 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 288 2 14 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 288 2 13 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 288 (accept_3_4 25 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 288 2 12 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 288 2 11 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 288 2 10 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 288 (accept_3_4 19 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 288 2 9 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 288 2 8 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 288 2 7 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 288 (accept_3_4 13 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 288 2 6 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 288 2 5 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 288 2 4 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 288 (accept_3_4 7 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  288 2 3 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 288 2 2 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 122 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 288 2 1 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 288 (accept_3_4 1 122 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 288 (allA_succ_of_accept 120 121 288 (Polychromatic418967fa.accept_17_1_2_16_1_5596 120 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 288 (accept_3_5 119 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  118 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 288
  (Polychromatic418967fa.accept_23_2_6_12_1_17749 117 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 121 288 (accept_3_5 116 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 115 121 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 288 (Polychromatic418967fa.accept_21_9_16_15_1_9014 114
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 288 (accept_3_5 113
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 288
  (Polychromatic418967fa.accept_25_12_21_13_1_17674 112 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 111 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 121 288 (accept_3_5 110 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 121 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 109 121
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 108 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 288 (accept_3_5 107 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 288 (Polychromatic418967fa.accept_21_1_16_15_1_8913 106 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 288 (Polychromatic418967fa.accept_19_10_7_3_1_6977 105 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 288 (accept_3_5 104 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  103 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 102 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 121 288 (accept_3_5 101 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 121 288 (Polychromatic418967fa.accept_19_5_7_3_1_6990 100 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 288 (Polychromatic418967fa.accept_10_9_1_8_1_755
  99 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 121 288 (accept_3_5 98
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 121 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 121 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 96 121 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 288 (accept_3_5 95 121 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  93 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 121 288 (accept_3_5 92
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 121 288
  (Polychromatic418967fa.accept_19_15_7_3_1_4143 91 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 121 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 288 (accept_3_5 89 121 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 121 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 88 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 288 (accept_3_5 86 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 85 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 84 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 288 (accept_3_5 83 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 288 (Polychromatic418967fa.accept_17_14_2_16_1_4380 82 121
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 288
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 81 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 288 (accept_3_5 80 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 288 (Polychromatic418967fa.accept_20_18_1_8_1_9326 78 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 288 (accept_3_5 77 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 288
  (Polychromatic418967fa.accept_22_9_11_2_1_267 75 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 288 (accept_3_5 74 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 288 (Polychromatic418967fa.accept_19_15_7_3_1_4143 72 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 288 (accept_3_5 71 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 70 121
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 288 (accept_3_5 68 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 288 (Polychromatic418967fa.accept_19_10_7_3_1_6977 67 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 288 (accept_3_5 65 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 64 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 288 (accept_3_5 62 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 288 (Polychromatic418967fa.accept_19_4_7_3_1_2893 61 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 288 (Polychromatic418967fa.accept_21_18_16_15_1_2864 60 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 288 (accept_3_5 59 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 58 121
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 57 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 288 (accept_3_5 56 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 288 (Polychromatic418967fa.accept_23_8_6_12_1_17664 54 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 288 (accept_3_5 53 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 288 (accept_3_5 50 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 288 (accept_3_5 47 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 288 (Polychromatic418967fa.accept_27_19_13_18_1_10216 46 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 288 (accept_3_5 44 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 288 (Polychromatic418967fa.accept_17_8_2_16_1_5598 42 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 288 (accept_3_5 41 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 288 (Polychromatic418967fa.accept_23_17_6_12_1_17748 40
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 288 (accept_3_5 38 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 288 (accept_3_5 35 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 288 (accept_3_5 32 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 288 (Polychromatic418967fa.accept_21_9_16_15_1_9014 30 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 288 (accept_3_5 29 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 121
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 288 (accept_3_5 26 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 288 (accept_3_5 23 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 288 (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 288
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 288 (accept_3_5 20 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 288 (accept_3_5 17 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 288 (Polychromatic418967fa.accept_22_16_11_2_1_16242 16
  121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 288
  (Polychromatic418967fa.accept_14_1_9_8_1_2863 15 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 288 (accept_3_5 14 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 288 (accept_3_5 11 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 288 (accept_3_5 8 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 288 (Polychromatic418967fa.accept_20_7_1_8_1_10806 7 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 288 (accept_3_5 5 121 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 121 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 288 (accept_3_5 2 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 121 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 288 (allA_succ_of_accept 119 120 288 (Polychromatic418967fa.accept_19_5_6_3_1_5578 119 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 288 2 59 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 120 288 3 39 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 120 288 4 29 30 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 115 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 120 288 6 19 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 120 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 113 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 288 8 14 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 120 288 3 37 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 120 288 2 55 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 109 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 288 12 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 107 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 288 2 53 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 288 3 35 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 288 8 13 15 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 103 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 120 288 6 17 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 120 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 101 120 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 288 4 25 30 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 120 288 3 33 40 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 120 288 2 49 60
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 288
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 97 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 120 288 24 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 120 288 (Polychromatic418967fa.accept_27_14_12_18_1_17747 95 120 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 288 2 47 60 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 120 288 3 31 40 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 120 288 4 23 30
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 288
  (Polychromatic418967fa.accept_22_3_10_2_1_17692 91 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 120 288 6 15 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 120 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 89 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 288 8 11 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 120 288 3 29 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 120 288 2 43 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 288
  (Polychromatic418967fa.accept_19_9_6_3_1_5563 85 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 288 12 7 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 83 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 288 2 41 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 120 288 3 27 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 120 288 8 10 15 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 288 6 13 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 288 4 19 30 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 288 3 25 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 288 2 37 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 288
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 73 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 288 24 3 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 288 (Polychromatic418967fa.accept_22_5_10_2_1_16257 71 120 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 288 2 35 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 120 288 3 23 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 288 4 17 30 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 67 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 288 6 11 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 288 (Polychromatic418967fa.accept_19_8_6_3_1_4164 65 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 288 8 8 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 288 3 21 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 288 2 31 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 288
  (Polychromatic418967fa.accept_13_9_3_2_1_399 61 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 288 12 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 288 (Polychromatic418967fa.accept_19_2_6_3_1_4182 59 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 288 2 29 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 288 3 19 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 288 8 7 15 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 288
  (Polychromatic418967fa.accept_19_17_6_3_1_9830 55 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 288 6 9 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 120 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 288 4 13 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 288 3 17 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 288 2 25 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 288 24 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 288 (Polychromatic418967fa.accept_19_9_6_3_1_5563 47 120 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 288 2 23 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 288 3 15 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 288 4 11 30 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 288
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 43 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 288 6 7 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 288 (Polychromatic418967fa.accept_23_18_5_12_1_11397 41 120 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 288 8 5 15 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 288 3 13 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 288 2 19 60 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 37 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 288 12 3 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 120 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 288 2 17 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 288 3 11 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 288 8 4 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 288 6 5 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 288 (Polychromatic418967fa.accept_17_12_1_16_1_4360 29 120 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 288 4 7 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 288 3 9 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 288 2 13 60 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 288 24 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 120 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 288 2 11 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 288 3 7 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 288 4 5 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 288 (Polychromatic418967fa.accept_17_2_1_16_1_6946
  19 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 288 6 3 20 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 288
  (Polychromatic418967fa.accept_19_17_6_3_1_9830 17 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 288 8 2 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 288 3 5 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 288 2 7 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 288 (Polychromatic418967fa.accept_22_13_10_2_1_5206 13 120 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 288 12 1 10 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 288 2 5 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 120 288 3 3 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 120 288 8 1 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 120 288 (Polychromatic418967fa.accept_19_7_6_3_1_6998 7 120 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 288 6 1 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5
  120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 288 4 1 30 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 288 3 1 40 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 288 2 1 60 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 120 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 288 (allA_succ_of_accept 118 119 288 (accept_3_4 118 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 117 119 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 288
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 116 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 119 288 (accept_3_4 115 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 114 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 119 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 113 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 288 (accept_3_4 112 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 111 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 119 288 (Polychromatic418967fa.accept_21_5_14_15_1_7290 110 119 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 288 (accept_3_4 109 119 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 119 288 (Polychromatic418967fa.accept_21_3_14_15_1_10526 108 119 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 107 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 288 (accept_3_4 106 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 119 288 (Polychromatic418967fa.accept_19_10_5_3_1_13818 105 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 104 119 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 288 (accept_3_4 103 119 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 288
  (Polychromatic418967fa.accept_19_7_5_3_1_13861 102 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 101 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 288 (accept_3_4 100 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 99 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 288
  (Polychromatic418967fa.accept_23_6_4_12_1_11383 98 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 119 288 (accept_3_4 97 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 119 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 96 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 95 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 288 (accept_3_4 94 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 288
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 93 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 119 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 92 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 288 (accept_3_4 91 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 119 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 90 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 288
  (Polychromatic418967fa.accept_20_9_19_8_1_1151 89 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 288 (accept_3_4 88 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 87 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 86 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 288 (accept_3_4 85 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 83 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 288 (accept_3_4 82 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 288 (Polychromatic418967fa.accept_21_17_14_15_1_5750 80 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 288 (accept_3_4 79 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 288 (Polychromatic418967fa.accept_19_2_5_3_1_5536 78 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 288 (accept_3_4 76 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 288 (Polychromatic418967fa.accept_21_12_14_15_1_8909 75 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 288 (accept_3_4 73 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 288 (Polychromatic418967fa.accept_21_9_14_15_1_11910 72
  119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 288 (accept_3_4 70 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 69 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 288 (Polychromatic418967fa.accept_21_5_14_15_1_7290 68 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 288 (accept_3_4 67 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 288 (Polychromatic418967fa.accept_21_3_14_15_1_10526 66
  119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 288
  (Polychromatic418967fa.accept_19_8_5_3_1_4181 65 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 288 (accept_3_4 64 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 288 (Polychromatic418967fa.accept_19_6_5_3_1_11210 63 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 288 (accept_3_4 61 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 288 (Polychromatic418967fa.accept_21_18_14_15_1_5809 60
  119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 59 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 288 (accept_3_4 58 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 288 (accept_3_4 55 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 288
  (Polychromatic418967fa.accept_25_3_19_13_1_17746 53 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 119 288 (accept_3_4 52 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 119 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 288 (Polychromatic418967fa.accept_21_8_14_15_1_5777 50 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 288 (accept_3_4 49 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 288 (accept_3_4 46 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 288 (Polychromatic418967fa.accept_19_7_5_3_1_13861 45 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 288 (accept_3_4 43 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 288 (Polychromatic418967fa.accept_25_17_19_13_1_12579 42 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 288 (accept_3_4 40 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 39 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 288
  (Polychromatic418967fa.accept_21_17_14_15_1_5750 38 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 119 288 (accept_3_4 37 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 119 288 (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 288 (Polychromatic418967fa.accept_19_16_5_3_1_1813 35 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 288 (accept_3_4 34 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 288
  (Polychromatic418967fa.accept_19_14_5_3_1_859 33 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 119 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 288 (accept_3_4 31 119 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 119 288 (Polychromatic418967fa.accept_21_9_14_15_1_11910 30 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 288 (accept_3_4 28 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 288 (accept_3_4 25 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 288
  (Polychromatic418967fa.accept_22_1_9_2_1_17745 23 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 288 (accept_3_4 22 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 288 (accept_3_4 19 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 119
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 288 (accept_3_4 16 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 288 (accept_3_4 13 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 288 (Polychromatic418967fa.accept_21_12_14_15_1_8909 12
  119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 288 (accept_3_4 10 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 288 (Polychromatic418967fa.accept_20_9_19_8_1_1151 9 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 288 (Polychromatic418967fa.accept_19_8_5_3_1_4181 8 119 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 288 (accept_3_4 7 119 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 288
  (Polychromatic418967fa.accept_21_5_14_15_1_7290 5 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 288 (accept_3_4 4 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 288 (Polychromatic418967fa.accept_21_3_14_15_1_10526 3 119 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 288 (accept_3_4 1 119 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 288 (allA_succ_of_accept 117 118 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 288 2 58 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 115 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 118 288 2 57 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 118 288 (accept_3_5 113 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 288 2 56 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 288 (Polychromatic418967fa.accept_19_16_4_3_1_2946 111 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 288 2 55 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 288
  (Polychromatic418967fa.accept_22_21_8_2_1_16285 109 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 118 288 2 54 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 118 288 (accept_3_5 107 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 288 2 53 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 105 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 288 2 52 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 288 2 51 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 288 (accept_3_5 101 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 288 2 50 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 99 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 288 2 49 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 97 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 288 2 48 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 288 (accept_3_5 95 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 288 2 47 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 288 2 46 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 91 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 288 2 45 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 288 (accept_3_5 89 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 288 2 44 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 87 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 288 2 43 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 288
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 85 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 118 288 2 42 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 118 288 (accept_3_5 83 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 288 2 41 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 81 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 288 2 40 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 288 2 39 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 288 (accept_3_5 77 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 288 2 38 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 288 2 37 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 288
  (Polychromatic418967fa.accept_19_16_4_3_1_2946 73 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 288 2 36 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 288 (accept_3_5 71 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 288 2 35 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 69 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 288 2 34 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 288
  (Polychromatic418967fa.accept_25_17_18_13_1_10808 67 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 118 288 2 33 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 118 288 (accept_3_5 65 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 288 2 32 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 288 2 31 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 288 2 30 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 288 (accept_3_5 59 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 288 2 29 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 288 2 28 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 288 2 27 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 288 (accept_3_5 53 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 288 2 26 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 288 2 25 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 288 2 24 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 288 (accept_3_5 47 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 288 2 23 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 288 2 22 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 288
  (Polychromatic418967fa.accept_20_3_18_8_1_4859 43 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 288 2 21 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 288 (accept_3_5 41 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 288 2 20 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 288 2 19 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 288 2 18 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 288 (accept_3_5 35 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 288 2 17 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 288 2 16 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 288
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 31 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 288 2 15 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 288 (accept_3_5 29 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 288 2 14 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 288 2 13 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 25 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 288 2 12 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 288 (accept_3_5 23 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 288 2 11 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 288 2 10 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 288 2 9 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 288 (accept_3_5 17 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 288 2 8 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 288 (Polychromatic418967fa.accept_22_15_8_2_1_14719 15 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 288 2 7 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 288
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 13 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 288 2 6 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 288 (accept_3_5 11 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 288 2 5 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 118 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 288 2 4 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 288 2 3 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 288 (accept_3_5 5 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  288 2 2 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 118 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 288 2 1 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 288 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 118 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 288 (allA_succ_of_accept 116 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 116 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 117 288 3 38 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 117 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 113 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 112 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 117 288 3 37 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 117 288 (Polychromatic418967fa.accept_20_10_17_8_1_4856 110 117 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 117 288 9 12 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 117 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 107 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 288
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 106 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 117 288 3 35 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 103 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 117 288 3 34 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 288
  (Polychromatic418967fa.accept_27_19_9_18_1_17744 100 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 117 288 9 11 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 117 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 98 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 117 288 3 32 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 94
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 117 288 3 31 39 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 117 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 92 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 288 (Polychromatic418967fa.accept_20_11_17_8_1_4903 91 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 117 288 9 10 13 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 89 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 117 288 3 29 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 117 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  86 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 117 288 3 28 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 82 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 117 288 9 9 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 79 117
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 288 3 26 39 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 288 3 25 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 74
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 288 9 8 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 117 288 (Polychromatic418967fa.accept_20_11_17_8_1_4903 71 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 288
  (Polychromatic418967fa.accept_20_10_17_8_1_4856 70 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 117 288 3 23 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 117 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 68 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 117 288 3 22 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 117 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 288 9 7 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 288 (Polychromatic418967fa.accept_21_19_12_15_1_7307 61
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 288 3 20 39 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 58 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 288 3 19 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 288
  (Polychromatic418967fa.accept_21_14_12_15_1_7299 56 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 288 9 6 13 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 288 3 17 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 288
  (Polychromatic418967fa.accept_20_10_17_8_1_4856 50 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 117 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 288 3 16 39 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 117 288 9 5 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 117 288
  (Polychromatic418967fa.accept_23_21_2_12_1_17743 44 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 117 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 117 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 288 3 14 39 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 288 (Polychromatic418967fa.accept_21_19_12_15_1_7307 40 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 288 3 13 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 288 9 4 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  35 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 288 3 11 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 288 3 10 39 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 288 9 3 13 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 288
  (Polychromatic418967fa.accept_21_5_12_15_1_11875 26 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 288 3 8 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 288
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 288 3 7 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 288 9 2 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 288 (Polychromatic418967fa.accept_27_16_9_18_1_17742 16
  117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 288 3 5 39 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 288
  (Polychromatic418967fa.accept_17_14_15_16_1_1271 14 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 288 3 4 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 288 9 1 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 117 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 288 3 2 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 288 3 1 39 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 117 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 288 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 117 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 288 (allA_succ_of_accept 115 116 288 (accept_3_4 115 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 288 2 57 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 113 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 288 4 28 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 111 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 116 288 2 55 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 116 288 (accept_3_4 109 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 288 4 27 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 107 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 288 2 53 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 105 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 288 4 26 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 288 (accept_3_4 103 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 288 2 51 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 116 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 288 4 25 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 288
  (Polychromatic418967fa.accept_22_11_6_2_1_16240 99 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 116 288 2 49 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 116 288 (accept_3_4 97 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 288 4 24 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 95 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 288 2 47 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 93 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 288 4 23 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 288 (accept_3_4 91 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 288 2 45 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 116 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 288 4 22 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 288 2 43 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 288 (accept_3_4 85 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 288 4 21 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 288 2 41 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 81 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 288 4 20 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 288 (accept_3_4 79 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 288 2 39 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 288 (Polychromatic418967fa.accept_19_1_2_3_1_6995 77 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 288 4 19 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 288 2 37 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 288 (accept_3_4 73 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 288 4 18 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 288 2 35 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 69 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 288 4 17 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 288 (accept_3_4 67 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 288 2 33 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 288 (Polychromatic418967fa.accept_27_11_8_18_1_14024 65 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 288 4 16 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 288 2 31 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 288 (accept_3_4 61 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 288 4 15 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 116 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 288 2 29 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 288 4 14 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 288 (accept_3_4 55 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 288 2 27 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 288 4 13 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 288 2 25 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 288 (accept_3_4 49 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 288 4 12 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 116 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 288 2 23 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 288 4 11 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 288 (accept_3_4 43 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 288 2 21 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 288 (Polychromatic418967fa.accept_22_19_6_2_1_16233 41 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 288 4 10 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 39 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 288 2 19 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 288 (accept_3_4 37 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 288 4 9 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 288 (Polychromatic418967fa.accept_19_16_2_3_1_5479 35 116 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 288 2 17 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 288 4 8 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 288 (accept_3_4 31
  116 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 288 2 15 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 288
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 288 4 7 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 116 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 288 2 13 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 288 (accept_3_4 25 116 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 288 4 6 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 116
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 288 2 11 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 288 4 5 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 288 (accept_3_4 19 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 288 2 9 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 288 4 4 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15
  116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 288 2 7 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 288 (accept_3_4 13
  116 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 288 4 3 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 11 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 288 2 5 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 116 288 (Polychromatic418967fa.accept_21_9_11_15_1_1600 9 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 288 4 2 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 288 (accept_3_4 7 116 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 288 2 3 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 288 4 1 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 288 2 1 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 288 (accept_3_4 1 116 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 288 (allA_succ_of_accept 114 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 288 (accept_3_5 113 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 112 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 111 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 115 288 (accept_3_5 110 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 108
  115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 288 (accept_3_5 107
  115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 288
  (Polychromatic418967fa.accept_19_11_1_3_1_5555 106 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 115 288 (Polychromatic418967fa.accept_17_3_13_16_1_2183 105 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 115 288 (accept_3_5 104 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 102 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 288 (accept_3_5 101 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 115 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 99 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 288 (accept_3_5 98 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 97 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 115 288 (accept_3_5 95 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 115 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 94 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 288 (accept_3_5 92 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 288 (Polychromatic418967fa.accept_21_7_10_15_1_8906 91 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 288
  (Polychromatic418967fa.accept_20_10_15_8_1_4818 90 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 115 288 (accept_3_5 89 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 288 (accept_3_5 86 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 115 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 115 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 288 (accept_3_5 83 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81
  115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 288 (accept_3_5 80
  115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216 78 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 288 (accept_3_5 77 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 288 (Polychromatic418967fa.accept_22_10_5_2_1_16254 76 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 288 (accept_3_5 74 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 73 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 288 (accept_3_5 71 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 70 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 288 (accept_3_5 68 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 66 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 288 (accept_3_5 65 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 288 (Polychromatic418967fa.accept_21_1_10_15_1_2828 64 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 288 (accept_3_5 62 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 288 (accept_3_5 59 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 288 (accept_3_5 56 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 288 (accept_3_5 53 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 288 (accept_3_5 50 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 288 (accept_3_5 47 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 288
  (Polychromatic418967fa.accept_20_5_15_8_1_4930 45 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 288 (accept_3_5 44 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 288 (accept_3_5 41 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 288 (accept_3_5 38 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 288 (accept_3_5 35 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 288 (Polychromatic418967fa.accept_20_14_15_8_1_9380 34 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 288 (accept_3_5 32 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 288 (Polychromatic418967fa.accept_25_6_15_13_1_17741 31 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 288 (accept_3_5 29 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 288 (accept_3_5 26 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 288 (accept_3_5 23 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 115
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 288 (accept_3_5 20 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 288 (accept_3_5 17 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 288
  (Polychromatic418967fa.accept_27_15_7_18_1_17740 15 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 115 288 (accept_3_5 14 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 115 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 115 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 288 (accept_3_5 11 115 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 288 (accept_3_5 8 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 288 (accept_3_5 5 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 288 (accept_3_5 2 115 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 288 (Polychromatic418967fa.accept_21_1_10_15_1_2828 1 115 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 288 (allA_succ_of_accept 113 114 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 113 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 288 2 56 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 114 288 3 37 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 114 288 2 55 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 109 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 288 6 18 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 107 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 114 288 2 53 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 114 288 3 35 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 114 288 2 52 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 103 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 114 288 6 17 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 114 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 114 288 2 50 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 114 288 3 33 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 114 288 2 49 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 288 6 16 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 95 114 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 288 2 47 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 114 288 3 31 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 114 288 2 46 57 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 288
  (Polychromatic418967fa.accept_21_7_9_15_1_5803 91 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 288 6 15 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 89 114 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 288 2 44 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 114 288 3 29 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 114 288 2 43 57 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 85 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 288 6 14 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 114 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 288 2 41 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 114 288 3 27 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 114 288 2 40 57 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 288 6 13 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 288 2 38 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 288 3 25 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 288 2 37 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 288 6 12 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 71 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 288 2 35 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 288 3 23 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 288 2 34 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 288
  (Polychromatic418967fa.accept_21_4_9_15_1_11925 67 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 114 288 6 11 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 114 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 288 2 32 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 288 3 21 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 288 2 31 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 288 6 10 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 114 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 288 2 29 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 288 3 19 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 288 2 28 57 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 288 6 9 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 288 2 26 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 288 3 17 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 288 2 25 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 288 6 8 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 288 2 23 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 288 3 15 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 288 2 22 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 43 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 288 6 7 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 288 2 20 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 288 3 13 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 288 2 19 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 288 6 6 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 288 2 17 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 288 3 11 38 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 288 2 16 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 288 6 5 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 288 2 14 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 288 3 9 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 288 2 13 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 114 288 6 4 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 114 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 114 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 288 2 11 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 288 3 7 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 288 2 10 57 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 288 6 3 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 288 2 8 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 288 3 5 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 288 2 7 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 288 6 2 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 114 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 288 2 5 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 288 3 3 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 288 2 4 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 288
  (Polychromatic418967fa.accept_21_7_9_15_1_5803 7 114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 288 6 1 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 114 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 288 2 2 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 288 3 1 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 288 2 1 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 1
  114 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 288 (allA_succ_of_accept 112 113 288 (accept_3_4 112 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 111 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 110 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 288 (accept_3_4 109 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 288
  (Polychromatic418967fa.accept_21_3_8_15_1_4301 108 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 113 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 107 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 288 (accept_3_4 106 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 105 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 288
  (Polychromatic418967fa.accept_19_9_18_3_1_5475 104 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 288 (accept_3_4 103 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 102 113 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  101 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 288 (accept_3_4
  100 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 99 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 98 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 288 (accept_3_4 97 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 96 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 95 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 113 288 (accept_3_4 94 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 113 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 93 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 113 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 92 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 288 (accept_3_4 91 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 90 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 89 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 288 (accept_3_4 88 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 87 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 288 (accept_3_4 85 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 84 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 288 (accept_3_4 82 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 81 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 80 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 288 (accept_3_4 79 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 78 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 77 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 113 288 (accept_3_4 76 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 113 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 113 288 (Polychromatic418967fa.accept_20_14_13_8_1_4847 74 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 288 (accept_3_4 73 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 71 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 288 (accept_3_4 70 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 68 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 288 (accept_3_4 67 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 288 (accept_3_4 64 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 288 (Polychromatic418967fa.accept_49_13_15_43_1_17739 62 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 288 (accept_3_4 61 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 288 (Polychromatic418967fa.accept_21_18_8_15_1_5745 60 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 59 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 288 (accept_3_4 58 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 288 (accept_3_4 55 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 288 (accept_3_4 52 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 50 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 288 (accept_3_4 49 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 288 (Polychromatic418967fa.accept_17_14_11_16_1_3261 48
  113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 288
  (Polychromatic418967fa.accept_19_9_18_3_1_5475 47 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 288 (accept_3_4 46 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 288 (accept_3_4 43 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 288 (accept_3_4 40 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 288 (Polychromatic418967fa.accept_20_18_13_8_1_9398 38 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 288 (accept_3_4 37 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 288 (accept_3_4 34 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 32 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 288 (accept_3_4 31 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 288 (accept_3_4 28 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 288 (accept_3_4 25 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 288 (accept_3_4 22 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 288 (accept_3_4 19 113 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 288
  (Polychromatic418967fa.accept_21_17_8_15_1_10549 17 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 113 288 (accept_3_4 16 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 113 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 288 (accept_3_4 13 113
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 113 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 288 (accept_3_4 10 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 113 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 113 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 288
  (Polychromatic418967fa.accept_30_8_23_18_1_17738 8 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 113 288 (accept_3_4 7 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 113 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 113 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 113 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 288 (accept_3_4 4 113 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486
  3 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 288 (accept_3_4 1 113 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 288 (allA_succ_of_accept 111 112 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 111 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 288 2 55 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 288
  (Polychromatic418967fa.accept_15_4_7_3_1_119 109 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 112 288 4 27 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 112 288 (accept_3_5 107 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 112 288 2 53 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 112 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 105 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 112 288 8 13 14 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 112 288
  (Polychromatic418967fa.accept_19_8_17_3_1_4154 103 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 112 288 2 51 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 112 288 (accept_3_5 101 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 112 288 4 25 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 112 288 (Polychromatic418967fa.accept_25_24_12_13_1_17737 99 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 288 2 49 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 288
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 97 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 112 288 16 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 112 288 (accept_3_5 95 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94
  112 288 2 47 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 93 112 288 (Polychromatic418967fa.accept_21_9_7_15_1_5769 93 112 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 288 4 23 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 112 288
  (Polychromatic418967fa.accept_17_6_10_16_1_9453 91 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 112 288 2 45 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 112 288 (accept_3_5 89 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 112 288 8 11 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 112 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 87 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 288 2 43 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 288 4 21 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 288 (accept_3_5 83 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 288 2 41 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 288 (Polychromatic418967fa.accept_19_5_17_3_1_4152 81 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 288 16 5 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 288
  (Polychromatic418967fa.accept_15_4_7_3_1_119 79 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 288 2 39 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 288 (accept_3_5 77 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 288 4 19 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 112 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 288 2 37 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 288
  (Polychromatic418967fa.accept_19_16_17_3_1_2916 73 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 112 288 8 9 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 112 288 (accept_3_5 71 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 288 2 35 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 288 (Polychromatic418967fa.accept_19_12_17_3_1_5515 69 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 288 4 17 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 288
  (Polychromatic418967fa.accept_25_17_12_13_1_17736 67 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 288 2 33 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 288 (accept_3_5 65 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 288 16 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 112 288 (Polychromatic418967fa.accept_19_6_17_3_1_11186 63 112 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 288 2 31 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 288
  (Polychromatic418967fa.accept_21_19_7_15_1_2848 61 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 112 288 4 15 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 112 288 (accept_3_5 59 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 288 2 29 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 288 8 7 14 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 288 2 27 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 288 (accept_3_5 53 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 288 4 13 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 288 (Polychromatic418967fa.accept_21_9_7_15_1_5769 51 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 288 2 25 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 288 16 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 112 288 (accept_3_5 47 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  112 288 2 23 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 112 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 112 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 288 4 11 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 288
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 43 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 112 288 2 21 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 112 288 (accept_3_5 41 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 288 8 5 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 112 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 39 112 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 288 2 19 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 288
  (Polychromatic418967fa.accept_27_10_4_18_1_2466 37 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 112 288 4 9 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 112 288 (accept_3_5 35 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 288 2 17 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 288 16 2 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 288
  (Polychromatic418967fa.accept_19_12_17_3_1_5515 31 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 112 288 2 15 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 112 288 (accept_3_5 29 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 288 4 7 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 112 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 112 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 288 2 13 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 288 (Polychromatic418967fa.accept_10_5_2_8_1_135
  25 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 288 8 3 14 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 288
  (accept_3_5 23 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 288 2 11 56 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 288
  (Polychromatic418967fa.accept_19_2_17_3_1_11224 21 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 112 288 4 5 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 112 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 288 2 9 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 288 (accept_3_5 17 112 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 288 16 1 7 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 288 2 7 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 112 288 (Polychromatic418967fa.accept_21_13_7_15_1_13450 13 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 288 4 3 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 288 (accept_3_5 11 112 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 288 2 5 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 288
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 288 8 1 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 112 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 288 2 3 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 288 (accept_3_5 5 112 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 288 4 1 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 112 288 (Polychromatic418967fa.accept_21_3_7_15_1_4300 3 112 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 288 2 1 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 288
  (Polychromatic418967fa.accept_19_1_17_3_1_1821 1 112 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 288 (allA_succ_of_accept 110 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 110 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 109 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 111 288 3 36 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 106 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 111 288 3 35 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 111 288 (Polychromatic418967fa.accept_21_20_6_15_1_11937 104 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 111 288 3 34 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 111 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 101 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 100 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 111 288 3 33 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 111 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 288
  (Polychromatic418967fa.accept_19_2_16_3_1_7005 97 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 111 288 3 32 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 111 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 95 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 288
  (Polychromatic418967fa.accept_19_18_16_3_1_1803 94 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 111 288 3 31 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 111 288 (Polychromatic418967fa.accept_21_8_6_15_1_5743 92 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 111 288 3 30 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 88 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 111 288 3 29 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 111 288 3 28 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 111 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407
  82 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 288 3 27 37 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 288 3 26 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067
  77 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 288 3 25 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 74 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 73 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 111 288 3 24 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 111 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 71 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 70 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 288 3 23 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 67 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 288 3 22 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 288
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 64 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 111 288 3 21 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 111 288 (Polychromatic418967fa.accept_19_5_16_3_1_1820 62 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 288 3 20 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 59 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 58
  111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 288 3 19 37 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 288 3 18 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  53 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 288
  (Polychromatic418967fa.accept_19_14_16_3_1_15089 52 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 111 288 3 17 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 111 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 50 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 49 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 288 3 16 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827
  46 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 288 3 15 37 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 288 3 14 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  41 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 288 3 13 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 288 (Polychromatic418967fa.accept_20_18_11_8_1_6367 38 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 288 3 12 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 288 3 11 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 111 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 31 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 288 3 10 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 288
  (Polychromatic418967fa.accept_22_6_1_2_1_17735 28 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 288 3 9 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 111
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 288 3 8 37 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 288 3 7 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 288 (Polychromatic418967fa.accept_15_5_6_3_1_525
  20 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 288 3 6 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 288 (Polychromatic418967fa.accept_19_17_16_3_1_8401 17 111 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16
  111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 288 3 5 37 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 288 3 4 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  11 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 288 3 3 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 111
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 288 3 2 37 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 288 (Polychromatic418967fa.accept_19_4_16_3_1_4175 4 111 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 288 3 1 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 111 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 288 (allA_succ_of_accept 109 110 288 (accept_3_4 109 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 288 2 54 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 288 (Polychromatic418967fa.accept_15_2_5_3_1_552 107 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 288 2 53 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 105 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 288 2 52 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 288 (accept_3_4 103 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 288 2 51 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 288 2 50 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 99 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 288 2 49 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 288 (accept_3_4 97 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 288 2 48 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 288 2 47 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 288
  (Polychromatic418967fa.accept_19_17_15_3_1_4174 93 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 110 288 2 46 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 110 288 (accept_3_4 91 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 288 2 45 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 288 (Polychromatic418967fa.accept_25_14_10_13_1_17734 89 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 288 2 44 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 288 2 43 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 288 (accept_3_4 85 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 288 2 42 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 288 2 41 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 288 2 40 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 288 (accept_3_4 79 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 288 2 39 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 288 2 38 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 288
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 75 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 288 2 37 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 288 (accept_3_4 73 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 288 2 36 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 288 (Polychromatic418967fa.accept_21_8_5_15_1_4208 71 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 288 2 35 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 288 2 34 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 288 (accept_3_4 67 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 288 2 33 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 288 (Polychromatic418967fa.accept_17_14_8_16_1_6863 65 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 288 2 32 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 288
  (Polychromatic418967fa.accept_23_17_18_12_1_9743 63 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 110 288 2 31 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 110 288 (accept_3_4 61 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 288 2 30 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 288 2 29 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 288
  (Polychromatic418967fa.accept_20_17_10_8_1_9374 57 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 110 288 2 28 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 110 288 (accept_3_4 55 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 288 2 27 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 288 2 26 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 288 2 25 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 288 (accept_3_4 49 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 288 2 24 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 288 2 23 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 288 2 22 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 288 (accept_3_4 43 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 288 2 21 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 288 2 20 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 288 2 19 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 288 (accept_3_4 37 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 288 2 18 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 288 2 17 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 288
  (Polychromatic418967fa.accept_21_12_5_15_1_17705 33 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 110 288 2 16 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 110 288 (accept_3_4 31 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 288 2 15 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 288 (Polychromatic418967fa.accept_19_10_15_3_1_5470 29 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 288 2 14 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 288 2 13 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 288 (accept_3_4 25 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 288 2 12 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 288 2 11 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 21 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 288 2 10 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 288 (accept_3_4 19 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 288 2 9 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 288 2 8 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 288
  (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 110 288 2 7 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 110 288 (accept_3_4 13 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 288 2 6 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 110 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 288 2 5 55 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 288 2 4 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 288 (accept_3_4 7 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  288 2 3 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 5 110 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 288 2 2 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 288 2 1 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 288 (accept_3_4 1 110 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 288 (allA_succ_of_accept 108 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 288 (accept_3_5 107 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 106 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 288
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 105 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 109 288 (accept_3_5 104 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 103 109 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 102
  109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 288 (accept_3_5 101
  109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 100 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 109 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 99 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 109 288 (accept_3_5 98 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 97 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 109 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 96 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 109 288 (accept_3_5 95 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 109 288 (Polychromatic418967fa.accept_17_8_7_16_1_9508 93 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 109 288 (accept_3_5 92 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 109 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 91 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 90 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 109 288 (accept_3_5 89 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 109 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 88 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 288 (accept_3_5 86 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 85 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 84 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 288 (accept_3_5 83 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 288 (accept_3_5 80 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 79 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 78 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 288 (accept_3_5 77 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 76 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 288 (accept_3_5 74 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 72 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 288 (accept_3_5 71 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 288 (Polychromatic418967fa.accept_22_4_21_2_1_3581 70 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 69 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 288 (accept_3_5 68 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 288 (accept_3_5 65 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 288 (Polychromatic418967fa.accept_22_19_21_2_1_17733 63 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 288 (accept_3_5 62 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 109 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 288 (accept_3_5 59 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 288 (Polychromatic418967fa.accept_22_14_21_2_1_14717 58 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 288 (accept_3_5 56 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 55 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 288 (accept_3_5 53 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 288 (accept_3_5 50 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 288 (accept_3_5 47 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 46 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 288 (accept_3_5 44 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 288 (accept_3_5 41 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 39 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 288 (accept_3_5 38 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 288 (accept_3_5 35 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 288 (accept_3_5 32 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 288 (accept_3_5 29 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 288 (Polychromatic418967fa.accept_19_9_14_3_1_2912 28 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 288 (accept_3_5 26 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 109
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 288 (accept_3_5 23 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 288 (accept_3_5 20 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 288 (accept_3_5 17 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 288 (Polychromatic418967fa.accept_25_15_9_13_1_17681 15 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 288 (accept_3_5 14 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 288 (Polychromatic418967fa.accept_22_13_21_2_1_17732 13
  109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 288 (accept_3_5 11 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 288 (accept_3_5 8 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 288
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 6 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 288 (accept_3_5 5 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 109 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 288 (accept_3_5 2 109 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 109 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 288 (allA_succ_of_accept 107 108 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 108 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 288 2 53 54 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 108 288 3 35 36 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 108 288 4 26 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 288 6 17 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 288 (Polychromatic418967fa.accept_21_17_3_15_1_5762 101 108 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 288 4 25 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 108 288 9 11 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 108 288 2 49 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 97 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 288 12 8 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 108 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 288 2 47 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 108 288 3 31 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 108 288 4 23 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 288
  (Polychromatic418967fa.accept_21_7_3_15_1_5800 91 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 288 18 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 108 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 288 4 22 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 288 3 29 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 108 288 2 43 54 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 288
  (Polychromatic418967fa.accept_19_9_13_3_1_9829 85 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 288 12 7 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 108 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 83 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 288 2 41 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 288 9 9 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 288 4 20 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 288 6 13 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 108 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 288 4 19 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 288 3 25 36 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 288 2 37 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 73 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 288 36 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 108 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 288 2 35 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 288 3 23 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 288 4 17 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 288 6 11 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 288 4 16 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 288 9 7 12 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 288 2 31 54 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 288 12 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 108 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 59 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 288 2 29 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 288 3 19 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 288 4 14 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 288
  (Polychromatic418967fa.accept_22_11_20_2_1_3577 55 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 108 288 18 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 108 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 288 4 13 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 288 3 17 36 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 288 2 25 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 288
  (Polychromatic418967fa.accept_19_11_13_3_1_9820 49 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 288 12 4 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 288 2 23 54 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 288 9 5 12 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 288 4 11 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 288
  (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 288 6 7 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 288 (Polychromatic418967fa.accept_17_7_6_16_1_2195 41 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 288 4 10 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 288 3 13 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 288 2 19 54 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 288 36 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 288 (Polychromatic418967fa.accept_19_16_13_3_1_5544 35 108 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 288 2 17 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 288 3 11 36 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 288 4 8 27 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 31 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 288 6 5 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 288 4 7 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 288 9 3 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 288 2 13 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 288 12 2 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 288 2 11 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 288 3 7 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 288 4 5 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 288 18 1 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 288
  (Polychromatic418967fa.accept_21_17_3_15_1_5762 17 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 288 4 4 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 288 3 5 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 288 2 7 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 288 (Polychromatic418967fa.accept_29_13_21_27_1_17731 13
  108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 288 12 1 9 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 288 2 5 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 108 288 9 1 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 108 288 4 2 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 108 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 108 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 288 6 1 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 288 4 1 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 288 3 1 36 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 288 2 1 54 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 288
  (Polychromatic418967fa.accept_21_1_3_15_1_5797 1 108 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 288 (allA_succ_of_accept 106 107 288 (accept_3_4 106 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  104 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 288 (accept_3_4
  103 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 102 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 288 (accept_3_4 100 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 288
  (Polychromatic418967fa.accept_25_23_7_13_1_17730 98 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 107 288 (accept_3_4 97 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 107 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 96 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 107 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 95 107
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 288 (accept_3_4 94 107
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 93 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 107 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 92 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 288 (accept_3_4 91 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  89 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 288 (accept_3_4 88
  107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 107 288 (Polychromatic418967fa.accept_17_1_5_16_1_5589 86 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 288 (accept_3_4 85 107 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 107 288 (Polychromatic418967fa.accept_25_9_7_13_1_17679 84 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 288 (accept_3_4 82 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 288 (Polychromatic418967fa.accept_20_1_7_8_1_4877 81 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 288 (accept_3_4 79 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 288 (Polychromatic418967fa.accept_19_2_12_3_1_5446 78 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 288 (accept_3_4 76 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 74 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 288 (accept_3_4 73 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 107
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 71 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 288 (accept_3_4 70 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 288 (Polychromatic418967fa.accept_19_11_12_3_1_8407 68 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 288 (accept_3_4 67 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 288 (accept_3_4 64 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 288 (accept_3_4 61 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 288 (accept_3_4 58 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 288 (Polychromatic418967fa.accept_22_12_19_2_1_11680 56 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 288 (accept_3_4 55 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 288 (Polychromatic418967fa.accept_29_25_20_27_1_17729 54
  107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 288 (accept_3_4 52 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 288 (accept_3_4 49 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 288
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 288 (accept_3_4 46 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 288 (accept_3_4 43 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 107
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 288 (accept_3_4 40 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 288 (accept_3_4 37 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 288 (accept_3_4 34 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 288 (Polychromatic418967fa.accept_22_11_19_2_1_17728 33 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 288 (Polychromatic418967fa.accept_19_13_12_3_1_5540 32 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 288 (accept_3_4 31 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 30 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 288 (accept_3_4 28 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 288
  (Polychromatic418967fa.accept_19_7_12_3_1_4169 26 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 288 (accept_3_4 25 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 288 (accept_3_4 22 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 288 (Polychromatic418967fa.accept_17_4_5_16_1_3240 21 107
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 288 (accept_3_4 19 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 288 (accept_3_4 16 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 288 (accept_3_4 13 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 288 (accept_3_4 10 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 107 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 288
  (Polychromatic418967fa.accept_21_8_2_15_1_17727 8 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 288 (accept_3_4 7 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 288 (accept_3_4 4 107 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 288
  (Polychromatic418967fa.accept_17_2_5_16_1_1264 2 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 288 (accept_3_4 1 107 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 288 (allA_succ_of_accept 105 106 288 (Polychromatic418967fa.accept_17_3_4_16_1_3208 105 106 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 288 2 52 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 103 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 106 288 2 51 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 106 288 (accept_3_5 101 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 106 288 2 50 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 106 288 (Polychromatic418967fa.accept_19_4_11_3_1_13801 99 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 106 288 2 49 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 106 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 97 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 106 288 2 48 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 106 288 (accept_3_5 95 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 106 288 2 47 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 106 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 93 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 288 2 46 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 288
  (Polychromatic418967fa.accept_21_7_1_15_1_680 91 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 288 2 45 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 288 (accept_3_5 89 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 288 2 44 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 288 (Polychromatic418967fa.accept_21_3_1_15_1_4287 87 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 288 2 43 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 288
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 85 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 288 2 42 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 288 (accept_3_5 83 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 288 2 41 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 81 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 288 2 40 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 79 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 288 2 39 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 288 (accept_3_5 77 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 288 2 38 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 288 2 37 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 73 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 288 2 36 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 288 (accept_3_5 71 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 288 2 35 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 288 (Polychromatic418967fa.accept_19_12_11_3_1_8399 69 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 288 2 34 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 288
  (Polychromatic418967fa.accept_19_10_11_3_1_12543 67 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 106 288 2 33 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 106 288 (accept_3_5 65 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 288 2 32 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 288 2 31 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 288
  (Polychromatic418967fa.accept_19_4_11_3_1_13801 61 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 106 288 2 30 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 106 288 (accept_3_5 59 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 288 2 29 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 288 (Polychromatic418967fa.accept_22_13_18_2_1_10024 57 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 288 2 28 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 288
  (Polychromatic418967fa.accept_27_1_25_18_1_8218 55 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 106 288 2 27 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 106 288 (accept_3_5 53 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 288 2 26 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 51 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 288 2 25 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 49 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 288 2 24 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 288 (accept_3_5 47 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 288 2 23 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 288 (Polychromatic418967fa.accept_21_3_1_15_1_4287 45 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 288 2 22 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 288 2 21 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 288 (accept_3_5 41 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 288 2 20 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 288 (Polychromatic418967fa.accept_17_5_4_16_1_6925 39 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 288 2 19 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 288
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 37 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 288 2 18 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 288 (accept_3_5 35 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 288 2 17 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 288 2 16 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 288 2 15 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 288 (accept_3_5 29 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 288 2 14 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 288 (Polychromatic418967fa.accept_19_8_11_3_1_5539 27 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 288 2 13 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 288
  (Polychromatic418967fa.accept_23_2_14_12_1_17726 25 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 106 288 2 12 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 106 288 (accept_3_5 23 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 288 2 11 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 288 2 10 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 288 2 9 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 288 (accept_3_5 17 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 288 2 8 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 288 (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 288 2 7 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 288 2 6 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 288 (accept_3_5 11 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 288 2 5 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 106 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 288 2 4 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 288
  (Polychromatic418967fa.accept_21_7_1_15_1_680 7 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 288 2 3 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 288 (accept_3_5 5 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  288 2 2 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 106 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 288 2 1 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 288 (Polychromatic418967fa.accept_19_1_11_3_1_5463 1 106 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 288 (allA_succ_of_accept 104 105 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 104 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 103 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 288 3 34 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 288 (Polychromatic418967fa.accept_25_1_5_13_1_12611 101 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 100 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 105 288 3 33 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 105 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 98 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 97 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 105 288 3 32 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 105 288 (Polychromatic418967fa.accept_20_15_5_8_1_4920 95 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 94 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 105 288 3 31 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 92 105 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 288
  (Polychromatic418967fa.accept_19_15_10_3_1_12550 91 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 105 288 3 30 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 105 288 (Polychromatic418967fa.accept_17_4_3_16_1_9483 89 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 288
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 88 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 105 288 3 29 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 105 288 (Polychromatic418967fa.accept_25_11_5_13_1_17725 86 105 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 85 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 105 288 3 28 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 105 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 82 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 105 288 3 27 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 105 288 (Polychromatic418967fa.accept_27_26_24_18_1_17724 80 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 288
  (Polychromatic418967fa.accept_23_10_13_12_1_17722 79 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 105 288 3 26 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 105 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 76 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 288 3 25 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 74 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 73 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 105 288 3 24 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 105 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 71 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 105 288 3 23 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 105 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 68 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 288 3 22 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 288 (Polychromatic418967fa.accept_27_11_24_18_1_17723 65 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 64 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 288 3 21 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 105 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  61 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 288 3 20 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 58 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 288 3 19 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 288
  (Polychromatic418967fa.accept_23_10_13_12_1_17722 56 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 105 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 288 3 18 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 288 3 17 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 288
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 50 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 105 288 (Polychromatic418967fa.accept_19_11_10_3_1_2934 49 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 288 3 16 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 288 (Polychromatic418967fa.accept_25_21_5_13_1_17721 46 105 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 288 3 15 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 288
  (Polychromatic418967fa.accept_25_19_5_13_1_17720 44 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 288 3 14 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 41 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 288 (Polychromatic418967fa.accept_26_14_1_2_1_10584 40 105 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 288 3 13 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 38 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 288 3 12 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  35 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 34 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 288 3 11 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 105 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 288
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 31 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 105 288 3 10 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 105 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 288
  (Polychromatic418967fa.accept_19_9_10_3_1_1738 28 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 288 3 9 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 105
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 288 3 8 35 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 288 3 7 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 288 (Polychromatic418967fa.accept_14_6_7_8_1_624
  20 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 288 3 6 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 105
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 288 3 5 35 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 288
  (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 288 3 4 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 288
  (Polychromatic418967fa.accept_19_11_10_3_1_2934 11 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 288 (Polychromatic418967fa.accept_20_10_5_8_1_6385 10 105 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 288 3 3 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 288
  (Polychromatic418967fa.accept_25_8_5_13_1_12597 8 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 288 3 2 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 288 (Polychromatic418967fa.accept_19_5_10_3_1_5460 5 105 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 4 105 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 288 3 1 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 105 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 105 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 288 (allA_succ_of_accept 103 104 288 (accept_3_4 103 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 288 2 51 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 101 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 288 4 25 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 99 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 288 2 49 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 288 (accept_3_4 97 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 288 8 12 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 288 (Polychromatic418967fa.accept_25_20_4_13_1_16080 95 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 288 2 47 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 288 4 23 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 288 (accept_3_4 91 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 288 2 45 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 288 8 11 13 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 288
  (Polychromatic418967fa.accept_19_11_9_3_1_4167 87 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 288 2 43 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 288 (accept_3_4 85 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 288 4 21 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 288 (Polychromatic418967fa.accept_27_2_23_18_1_17719 83 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 288 2 41 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 288
  (Polychromatic418967fa.accept_21_18_20_15_1_8916 81 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 104 288 8 10 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 104 288 (accept_3_4 79 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 288 2 39 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 77 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 288 4 19 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 288 2 37 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 288 (accept_3_4 73 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 288 8 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 71 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 288 2 35 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 288 4 17 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 288 (accept_3_4 67 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 288 2 33 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 288 8 8 13 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 288 2 31 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 288 (accept_3_4 61 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 288 4 15 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 288 2 29 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 288
  (Polychromatic418967fa.accept_22_13_16_2_1_8523 57 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 104 288 8 7 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 104 288 (accept_3_4 55 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 288 2 27 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 288 (Polychromatic418967fa.accept_19_15_9_3_1_13764 53 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 288 4 13 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 288 2 25 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 288 (accept_3_4 49 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 288 8 6 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 104 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 288 2 23 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 288
  (Polychromatic418967fa.accept_25_20_4_13_1_16080 45 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 104 288 4 11 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 104 288 (accept_3_4 43 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 288 2 21 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 288 8 5 13 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 288 2 19 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 288 (accept_3_4 37 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 288 4 9 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 104 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 288 2 17 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 288 8 4 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 288 (accept_3_4 31
  104 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 288 2 15 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 288 4 7 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 288 (Polychromatic418967fa.accept_21_6_20_15_1_10532 27 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 288 2 13 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 288 (accept_3_4 25 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 288 8 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 288 2 11 52 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 288 4 5 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 288 (accept_3_4 19 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 288 2 9 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 104 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 288 8 2 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 288
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 15 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 104 288 2 7 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 104 288 (accept_3_4 13 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 288 4 3 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 104 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 104 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 288 2 5 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 288 8 1 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 288 (accept_3_4 7 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  288 2 3 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 288 4 1 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 288 (Polychromatic418967fa.accept_22_3_16_2_1_10045 3 104 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 288 2 1 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 288 (accept_3_4 1 104 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 288 (allA_succ_of_accept 102 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 288 (accept_3_5 101 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 288 (Polychromatic418967fa.accept_15_10_13_3_1_4816 100 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 99 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 288 (accept_3_5 98 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 96 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 288 (accept_3_5 95 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 288
  (Polychromatic418967fa.accept_19_17_8_3_1_11211 93 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 103 288 (accept_3_5 92 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 103 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 91 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 288 (accept_3_5 89 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418
  88 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 288 (accept_3_5 86 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 288 (accept_3_5 83 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 82 103
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 288 (accept_3_5 80 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 79 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 78 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 288 (accept_3_5 77 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 288 (accept_3_5 74 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 288 (accept_3_5 71 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 70 103
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 288 (accept_3_5 68 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 288 (accept_3_5 65 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 288
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 288 (accept_3_5 62 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 288 (accept_3_5 59 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 58 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 103 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 288 (accept_3_5 56 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 288 (Polychromatic418967fa.accept_15_9_13_3_1_535
  54 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 288 (accept_3_5 53
  103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 103 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 288 (accept_3_5 50 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 103 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 288 (accept_3_5 47 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 288 (accept_3_5 44 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 42 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 288 (accept_3_5 41 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 40 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 288 (accept_3_5 38 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 288 (Polychromatic418967fa.accept_23_14_11_12_1_16206 37 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 288 (accept_3_5 35 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 288 (Polychromatic418967fa.accept_19_14_8_3_1_6981 33 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 288 (accept_3_5 32 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 288 (accept_3_5 29 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 288 (accept_3_5 26 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 288 (accept_3_5 23 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 22 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 288 (accept_3_5 20 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 103
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 288 (accept_3_5 17 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 288 (accept_3_5 14 103 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 103 288 (accept_3_5 11 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 288 (accept_3_5 8 103 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 288
  (Polychromatic418967fa.accept_21_7_19_15_1_4201 7 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 103 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 288 (accept_3_5 5 103 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 103 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 288 (accept_3_5 2 103
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 1 103 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 103
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 288 (allA_succ_of_accept 101 102 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 102 288 2 50 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 102 288 3 33 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 102 288 2 49 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 97 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 288 6 16 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 102 288 2 47 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 288 3 31 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 102 288 2 46 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 288
  (Polychromatic418967fa.accept_19_15_7_3_1_4143 91 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 288 6 15 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 288 2 44 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 288 3 29 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 288 2 43 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 288 6 14 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 83 102 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 288 2 41 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 288 3 27 34 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 288 2 40 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 288
  (Polychromatic418967fa.accept_21_16_18_15_1_7282 79 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 102 288 6 13 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 102 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 102 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 288 2 38 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 288 3 25 34 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 288 2 37 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 288 6 12 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491 71 102 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 288 2 35 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 288 3 23 34 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 288 2 34 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 288 6 11 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 288 2 32 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 288 3 21 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 288 2 31 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 288 6 10 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 288 2 29 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 288 3 19 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 288 2 28 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 288 6 9 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 288 2 26 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 288 3 17 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 288 2 25 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 102 288 6 8 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 102 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 288 2 23 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 288 3 15 34 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 288 2 22 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 288 6 7 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 288 (Polychromatic418967fa.accept_21_20_18_15_1_11881 41 102 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 288 2 20 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 288 3 13 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 288 2 19 51 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 288 6 6 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 288 2 17 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 288 3 11 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 288 2 16 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 288 6 5 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 288 2 14 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 288 3 9 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 288 2 13 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 288 6 4 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 288 2 11 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 288 3 7 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 288 2 10 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 288 6 3 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 288 2 8 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 288 3 5 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 288 2 7 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 102 288 6 2 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 102 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 102 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 288 2 5 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 288 3 3 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 288 2 4 51 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 288 6 1 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 288 2 2 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 288 3 1 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 288 2 1 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1
  102 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 288 (allA_succ_of_accept 100 101 288 (accept_3_4 100 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 99 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 98 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 288 (accept_3_4 97 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 288 (accept_3_4 94 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 288
  (Polychromatic418967fa.accept_19_16_6_3_1_6972 92 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 288 (accept_3_4 91 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 288 (accept_3_4 88 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 288 (Polychromatic418967fa.accept_20_7_1_8_1_10806 87 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 288 (accept_3_4 85 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 84 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 288 (accept_3_4 82 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 288
  (Polychromatic418967fa.accept_19_4_6_3_1_15078 80 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 288 (accept_3_4 79 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 288 (Polychromatic418967fa.accept_19_2_6_3_1_4182 78 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 288 (accept_3_4 76 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 288 (accept_3_4 73 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 71 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 288 (accept_3_4 70 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 288 (accept_3_4 67 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 66 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 288 (accept_3_4 64 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 288
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 62 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 288 (accept_3_4 61 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 59 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 288 (accept_3_4 58 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 57 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 288
  (Polychromatic418967fa.accept_19_18_6_3_1_8405 56 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 288 (accept_3_4 55 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 288 (accept_3_4 52 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 101 288 (accept_3_4 49 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 101 288 (Polychromatic418967fa.accept_21_6_17_15_1_2833 48 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424
  47 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 288 (accept_3_4 46
  101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 288 (accept_3_4 43 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 101 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 288
  (Polychromatic418967fa.accept_22_19_13_2_1_17718 41 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 101 288 (accept_3_4 40 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 288 (accept_3_4 37 101
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 101 288 (Polychromatic418967fa.accept_19_16_6_3_1_6972 35 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 288 (accept_3_4 34 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 288 (accept_3_4 31
  101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 101 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 288 (accept_3_4 28 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 101 288 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 288 (accept_3_4 25 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 288 (accept_3_4 22 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 288
  (Polychromatic418967fa.accept_19_1_6_3_1_6968 20 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 288 (accept_3_4 19 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 288 (Polychromatic418967fa.accept_19_17_6_3_1_9830 17 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 288 (accept_3_4 16 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 288 (Polychromatic418967fa.accept_22_15_13_2_1_13218 15
  101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 101 288 (accept_3_4 13 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 288 (accept_3_4 10 101 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 288 (accept_3_4 7 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 288 (accept_3_4 4 101 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 101 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 288 (accept_3_4 1 101 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_288_segment_000))))))))))))))))))))))))))))))))))))))))


