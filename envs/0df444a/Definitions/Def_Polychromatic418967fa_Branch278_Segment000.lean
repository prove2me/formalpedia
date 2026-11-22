-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch278_Segment000
-- name    : Polychromatic418967fa_Branch278_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:50:52.603421+00:00
-- url     : https://prove2.me/theorems/83636f55-b0b7-460a-9ee7-e1e9b177f822
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

def Polychromatic418967fa.branch_278_segment_000 : allB 123 278 :=
  allB_succ 122 278 (allA_succ_of_accept 121 122 278 (accept_3_2 121 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 278 2 60 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 278 2 59 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 278
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 117 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 122 278 2 58 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 122 278 (accept_3_2 115 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 278 2 57 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 113 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 278 2 56 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 111 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 278 2 55 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 278 (accept_3_2 109 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 278 2 54 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 107 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 278 2 53 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 105 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 278 2 52 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 278 (accept_3_2 103 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 278 2 51 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 278 2 50 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 278 2 49 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 278 (accept_3_2 97 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 278 2 48 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 278 2 47 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 278 2 46 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 278 (accept_3_2 91 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 278 2 45 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 278 (Polychromatic418967fa.accept_14_5_10_12_1_1454 89 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 278 2 44 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 278 2 43 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 278 (accept_3_2 85 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 278 2 42 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 278 2 41 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 278
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 81 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 278 2 40 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 278 (accept_3_2 79 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 278 2 39 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 278 (Polychromatic418967fa.accept_17_9_3_6_1_11232 77 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 278 2 38 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 278 2 37 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 278 (accept_3_2 73 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 278 2 36 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 278 2 35 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 278 2 34 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 278 (accept_3_2 67 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 278 2 33 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 278 2 32 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 278
  (Polychromatic418967fa.accept_19_6_8_12_1_6271 63 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 278 2 31 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 278 (accept_3_2 61 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 278 2 30 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 59 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 278 2 29 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 278 2 28 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 278 (accept_3_2 55 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 278 2 27 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 278 (Polychromatic418967fa.accept_19_15_8_12_1_1286 53 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 278 2 26 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 278 2 25 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 278 (accept_3_2 49 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 278 2 24 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 278 2 23 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 278 2 22 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 278 (accept_3_2 43 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 278 2 21 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 278 2 20 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 278 2 19 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 278 (accept_3_2 37 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 278 2 18 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 278 2 17 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 278 2 16 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 278 (accept_3_2 31 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 278 2 15 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 278 2 14 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 278
  (Polychromatic418967fa.accept_20_7_2_18_1_5618 27 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 278 2 13 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 278 (accept_3_2 25 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 278 2 12 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 278 2 11 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 278 2 10 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 278 (accept_3_2 19 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 278 2 9 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 278 (Polychromatic418967fa.accept_20_17_2_18_1_11576 17 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 278 2 8 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 278 2 7 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 278 (accept_3_2 13 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 278 2 6 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 278 2 5 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 278 2 4 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 278 (accept_3_2 7 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  278 2 3 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 122 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 278 2 2 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 122 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 278 2 1 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 278 (accept_3_2 1 122 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 278 (allA_of_3_0 121 121 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 278
  (allA_succ_of_accept 119 120 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 120 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 278 2 59 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 278 (Polychromatic418967fa.accept_11_7_10_3_1_633
  117 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 278 2 58 60 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 278
  (accept_3_2 115 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 120 278 2 57 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 120 278 2 56 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 120 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 111 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 278 2 55 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 278 (accept_3_2 109 120 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 278 2 54 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 278
  (Polychromatic418967fa.accept_17_5_1_6_1_2615 107 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 278 2 53 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 120 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 120 278 2 52 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 278 (accept_3_2 103 120 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 278 2 51 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 101 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 278 2 50 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 99 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 278 2 49 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 278 (accept_3_2 97 120 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 278 2 48 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 120 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 95 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 120 278 2 47 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 120 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 93 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 278 2 46 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 278 (accept_3_2 91 120 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 278 2 45 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 278
  (Polychromatic418967fa.accept_13_11_3_5_1_982 89 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 278 2 44 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 278 2 43 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 278 (accept_3_2 85 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 120 278 2 42 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 83
  120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 278 2 41 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 278 2 40 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 278 (accept_3_2 79 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 278 2 39 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 278 2 38 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 278
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 75 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 278 2 37 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 278 (accept_3_2 73 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 278 2 36 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 278 (Polychromatic418967fa.accept_13_6_3_5_1_3167 71 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 278 2 35 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 278 2 34 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 278 (accept_3_2 67 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 278 2 33 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 278 2 32 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 278
  (Polychromatic418967fa.accept_13_11_3_5_1_982 63 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 278 2 31 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 278 (accept_3_2 61 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 278 2 30 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 278 2 29 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 278
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 57 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 278 2 28 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 278 (accept_3_2 55 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 278 2 27 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 278 2 26 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 278 2 25 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 278 (accept_3_2 49 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 278 2 24 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 278 2 23 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 278 2 22 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 278 (accept_3_2 43 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 278 2 21 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 278 2 20 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 278 2 19 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 278 (accept_3_2 37 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 278 2 18 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 278 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 278 2 17 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 278 2 16 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 120 278 (accept_3_2 31 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 278 2 15 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 278 2 14 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 278 2 13 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 278 (accept_3_2 25 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 278 2 12 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 278 2 11 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 278
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 278 2 10 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 278 (accept_3_2 19 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 278 2 9 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 278 2 8 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 120 278 2 7 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 278 (accept_3_2 13 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 278 2 6 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 120 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 278 2 5 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 278
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 278 2 4 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 278 (accept_3_2 7 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  278 2 3 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 278 2 2 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 120 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 278 2 1 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 278 (accept_3_2 1 120 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 278 (allA_succ_of_accept 118 119 278 (accept_3_2 118 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 119 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 116 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 278 (accept_3_2 115 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 114 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 119 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 278 (accept_3_2 112 119 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 278
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 110 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 119 278 (accept_3_2 109 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 119 278 (Polychromatic418967fa.accept_13_4_2_5_1_4045 108 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 278
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 107 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 278 (accept_3_2 106 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 278 (accept_3_2 103 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 119 278 (accept_3_2 100 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 119 278 (Polychromatic418967fa.accept_13_7_2_5_1_2344 98 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 278 (accept_3_2 97 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 278 (accept_3_2 94 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 278 (accept_3_2 91 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 278 (Polychromatic418967fa.accept_13_12_2_5_1_1634 90 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 278 (accept_3_2 88 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 278 (accept_3_2 85 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 278
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 83 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 278 (accept_3_2 82 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 278 (accept_3_2 79 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 278 (accept_3_2 76 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 278 (accept_3_2 73 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 278
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 278 (accept_3_2 70 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 278 (accept_3_2 67 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 278 (accept_3_2 64 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 278 (Polychromatic418967fa.accept_13_10_2_5_1_1633 62 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 278 (accept_3_2 61 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 278 (accept_3_2 58 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 278 (accept_3_2 55 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 278 (accept_3_2 52 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 278 (accept_3_2 49 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 278
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 278 (accept_3_2 46 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 278 (accept_3_2 43 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 278 (accept_3_2 40 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 278 (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 278 (accept_3_2 37 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 278 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 278
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 278 (accept_3_2 34 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 278 (accept_3_2 31 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 278 (accept_3_2 28 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 278 (Polychromatic418967fa.accept_19_7_5_12_1_7756 26 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 278 (accept_3_2 25 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 278 (accept_3_2 22 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 278 (accept_3_2 19 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 278 (Polychromatic418967fa.accept_21_18_14_5_1_8193 18 119
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 278 (accept_3_2 16 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 278 (accept_3_2 13 119 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 278
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 278 (accept_3_2 10 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 278 (accept_3_2 7 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 278 (accept_3_2 4 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 278 (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 278 (accept_3_2 1 119 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 278 (allA_of_3_0 118 118 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 278
  (allA_succ_of_accept 116 117 278 (Polychromatic418967fa.accept_15_11_12_8_1_739 116 117 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 278 (accept_3_2 115 117 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 114 117 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 278 (accept_3_2 112 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 278 (Polychromatic418967fa.accept_15_5_12_8_1_3168 110 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 278 (accept_3_2 109 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 108
  117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 278 (accept_3_2 106 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 278 (Polychromatic418967fa.accept_19_9_3_12_1_6191 104 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 278 (accept_3_2 103 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 102 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 278 (accept_3_2 100 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 278 (Polychromatic418967fa.accept_11_10_7_3_1_3679 98 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 278 (accept_3_2 97 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 278 (Polychromatic418967fa.accept_18_6_9_8_1_6812 96 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 278 (accept_3_2 94 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 93 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 92 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 278 (accept_3_2 91 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 278 (accept_3_2 88 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 278 (Polychromatic418967fa.accept_15_11_12_8_1_739 86 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 278 (accept_3_2 85 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 278 (Polychromatic418967fa.accept_16_4_5_6_1_8071 84 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 278 (accept_3_2 82 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 80 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 278 (accept_3_2 79 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 278 (accept_3_2 76 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 278 (Polychromatic418967fa.accept_19_17_3_12_1_13140 74 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 278 (accept_3_2 73 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 278 (Polychromatic418967fa.accept_19_15_3_12_1_11789 72
  117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 278 (accept_3_2 70 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 278 (Polychromatic418967fa.accept_16_4_5_6_1_8071 68 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 278 (accept_3_2 67 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 278 (accept_3_2 64 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 278 (Polychromatic418967fa.accept_20_2_17_18_1_11496 62 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 278 (accept_3_2 61 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 278 (Polychromatic418967fa.accept_17_9_15_6_1_3744 60 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 278 (accept_3_2 58 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 278 (Polychromatic418967fa.accept_18_3_9_8_1_2977 57 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 278 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 278 (accept_3_2 55 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 278 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 278 (accept_3_2 52 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 278 (Polychromatic418967fa.accept_15_5_12_8_1_3168 50 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 278 (accept_3_2 49 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 48 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 278 (accept_3_2 46 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 278 (Polychromatic418967fa.accept_27_17_9_8_1_9550 44 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 278 (accept_3_2 43 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 278 (accept_3_2 40 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 38 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 278 (accept_3_2 37 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 278 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 278 (accept_3_2 34 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 278 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 278 (accept_3_2 31 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 278 (accept_3_2 28 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 278 (accept_3_2 25 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 278 (accept_3_2 22 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 278 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 278 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 278 (accept_3_2 19 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 117
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 278 (accept_3_2 16 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 278 (Polychromatic418967fa.accept_17_14_15_6_1_4819 14 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 278 (accept_3_2 13 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 278 (Polychromatic418967fa.accept_25_12_17_3_1_17052 12
  117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 278 (accept_3_2 10 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 278 (Polychromatic418967fa.accept_17_8_15_6_1_4889 8 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 278 (accept_3_2 7 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 117 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 278 (accept_3_2 4 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 278 (Polychromatic418967fa.accept_19_2_3_12_1_10559 2 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 278 (accept_3_2 1 117 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 278 (allA_succ_of_accept 115 116 278 (accept_3_2 115 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 278 2 57 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 113 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 278 2 56 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 111 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 278 2 55 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 278 (accept_3_2 109 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 278 2 54 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 107 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 278 2 53 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 278
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 105 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 116 278 2 52 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 116 278 (accept_3_2 103 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 278 2 51 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 101 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 278 2 50 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 278 2 49 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 278 (accept_3_2 97 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 278 2 48 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 95 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 278 2 47 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 278 2 46 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 278 (accept_3_2 91 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 278 2 45 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 278 2 44 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 278
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 87 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 116 278 2 43 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 116 278 (accept_3_2 85 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 278 2 42 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 278 2 41 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 278
  (Polychromatic418967fa.accept_20_1_16_18_1_1677 81 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 116 278 2 40 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 116 278 (accept_3_2 79 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 278 2 39 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 278 2 38 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 278
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 75 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 278 2 37 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 278 (accept_3_2 73 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 278 2 36 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 278 2 35 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 278 2 34 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 278 (accept_3_2 67 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 278 2 33 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 278 2 32 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 278 2 31 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 278 (accept_3_2 61 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 278 2 30 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 278 2 29 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 278 2 28 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 278 (accept_3_2 55 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 278 2 27 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 278 2 26 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 278 2 25 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 278 (accept_3_2 49 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 278 2 24 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 278 2 23 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 278
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 278 2 22 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 278 (accept_3_2 43 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 278 2 21 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 278 2 20 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 278
  (Polychromatic418967fa.accept_19_1_2_12_1_7725 39 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 278 2 19 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 278 (accept_3_2 37 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 278 2 18 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 278 2 17 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 278 2 16 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 278 (accept_3_2 31 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 278 2 15 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 278 2 14 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 278 2 13 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 278 (accept_3_2 25 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 278 2 12 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 278 2 11 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 278
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 278 2 10 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 278 (accept_3_2 19 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 278 2 9 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 116 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 278 2 8 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 278 2 7 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 278 (accept_3_2 13 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 278 2 6 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 116 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 278 2 5 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 278 2 4 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 278 (accept_3_2 7 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  278 2 3 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 116 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 278 2 2 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 116 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 116 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 278 2 1 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 278 (accept_3_2 1 116 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 278 (allA_of_3_0 115 115 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 278
  (allA_succ_of_accept 113 114 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 113 114 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 278 2 56 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 278 (Polychromatic418967fa.accept_9_3_6_8_1_308
  111 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 278 2 55 57 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 278
  (accept_3_2 109 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 278 2 54 57 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 278
  (Polychromatic418967fa.accept_15_2_9_8_1_736 107 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 278 2 53 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 105 114 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 278 2 52 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 278 (accept_3_2 103 114 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 278 2 51 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 101 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 278 2 50 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 99 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 278 2 49 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 278 (accept_3_2 97 114 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 278 2 48 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 95
  114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 278 2 47 57 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 93 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 278 2 46 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 278 (accept_3_2 91 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 278 2 45 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 89 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 278 2 44 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 278 2 43 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 278 (accept_3_2 85 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 278 2 42 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 278 2 41 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 278 2 40 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 278 (accept_3_2 79 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 278 2 39 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 278 2 38 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 278 2 37 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 278 (accept_3_2 73 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 278 2 36 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 278 (Polychromatic418967fa.accept_13_6_10_5_1_1648 71 114 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 278 2 35 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 278 2 34 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 278 (accept_3_2 67 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 278 2 33 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 278 2 32 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 278 2 31 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 278 (accept_3_2 61 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 278 2 30 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 278 2 29 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 278 2 28 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 278 (accept_3_2 55 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 278 2 27 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 278 2 26 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 278
  (Polychromatic418967fa.accept_11_7_4_3_1_302 51 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 278 2 25 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 278 (accept_3_2 49 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 278 2 24 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 278 2 23 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 278 2 22 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 278 (accept_3_2 43 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 278 2 21 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 278 2 20 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 278 2 19 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 278 (accept_3_2 37 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 278 2 18 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 278 (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 114 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 278 2 17 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 278 2 16 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 278 (accept_3_2 31 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 278 2 15 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 278 2 14 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 278 2 13 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 278 (accept_3_2 25 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 278 2 12 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 278 2 11 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 278 2 10 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 278 (accept_3_2 19 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 278 2 9 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 278 2 8 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 278 2 7 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 278 (accept_3_2 13 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 278 2 6 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 278 2 5 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 278 2 4 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 278 (accept_3_2 7 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  278 2 3 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 278 2 2 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 278 2 1 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 278 (accept_3_2 1 114 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 278 (allA_succ_of_accept 112 113 278 (accept_3_2 112 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 113 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 113
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 278 (accept_3_2 109 113
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 108 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 113 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 278 (accept_3_2 106 113 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 104 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 278 (accept_3_2 103 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 278 (accept_3_2 100 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 113 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 278
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 98 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 278 (accept_3_2 97 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 278 (accept_3_2 94 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 278 (accept_3_2 91 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 278 (Polychromatic418967fa.accept_17_4_11_6_1_3730 89 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 278 (accept_3_2 88 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 113 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 278 (accept_3_2 85 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 278 (accept_3_2 82 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 278 (accept_3_2 79 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 278 (Polychromatic418967fa.accept_19_1_18_12_1_7755 77 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 278 (accept_3_2 76 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 278 (accept_3_2 73 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 278 (Polychromatic418967fa.accept_17_4_11_6_1_3730 72 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 278 (accept_3_2 70 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 68 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 278 (accept_3_2 67 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 278 (accept_3_2 64 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 278 (accept_3_2 61 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 278 (accept_3_2 58 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 278 (accept_3_2 55 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 278 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 278 (accept_3_2 52 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 278
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 278 (accept_3_2 49 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 278 (accept_3_2 46 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 278 (accept_3_2 43 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 278 (accept_3_2 40 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 278 (accept_3_2 37 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 278 (accept_3_2 34 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 278 (accept_3_2 31 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 278 (accept_3_2 28 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 278 (accept_3_2 25 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 278 (accept_3_2 22 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 278 (accept_3_2 19 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 278 (accept_3_2 16 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 278
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 278 (accept_3_2 13 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 278 (accept_3_2 10 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 278 (accept_3_2 7 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 278 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 278 (accept_3_2 4 113 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 278 (accept_3_2 1 113 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 278 (allA_of_3_0 112 112 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 278
  (allA_succ_of_accept 110 111 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 111 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 278 (accept_3_2 109 111 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 278 (Polychromatic418967fa.accept_19_13_16_12_1_6096 108 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 278 (accept_3_2 106 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 278 (accept_3_2 103 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 102 111
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 278 (accept_3_2 100 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 278 (Polychromatic418967fa.accept_22_10_1_14_1_9335 98 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 278 (accept_3_2 97 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 278 (accept_3_2 94 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 92 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 278 (accept_3_2 91 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 90 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 278 (accept_3_2 88 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 278 (accept_3_2 85 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 278 (Polychromatic418967fa.accept_17_16_9_6_1_3723 84 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 278 (accept_3_2 82 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 278 (Polychromatic418967fa.accept_13_2_7_5_1_3189 80 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 278 (accept_3_2 79 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 278 (accept_3_2 76 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 278 (Polychromatic418967fa.accept_21_12_6_5_1_3484 75 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 278 (accept_3_2 73 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 278 (Polychromatic418967fa.accept_19_15_16_12_1_4779 72 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 278 (accept_3_2 70 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 278 (accept_3_2 67 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 278 (accept_3_2 64 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 278 (Polychromatic418967fa.accept_14_6_13_12_1_810 62 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 278 (accept_3_2 61 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 278 (accept_3_2 58 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 278 (accept_3_2 55 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 278 (accept_3_2 52 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 278 (accept_3_2 49 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 278 (Polychromatic418967fa.accept_14_6_13_12_1_810 48 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 278 (accept_3_2 46 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 278 (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 278 (accept_3_2 43 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 278 (accept_3_2 40 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 278 (accept_3_2 37 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 278 (accept_3_2 34 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 278 (accept_3_2 31 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 278 (accept_3_2 28 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 278 (Polychromatic418967fa.accept_18_9_3_8_1_5419 27 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 278 (Polychromatic418967fa.accept_19_7_16_12_1_10556 26 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 278 (accept_3_2 25 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 278 (accept_3_2 22 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 278 (accept_3_2 19 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 278 (accept_3_2 16 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 278 (accept_3_2 13 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 278 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 111 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 278 (accept_3_2 10 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 278 (accept_3_2 7 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 278 (accept_3_2 4 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 111 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 278 (accept_3_2 1 111 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 278 (allA_succ_of_accept 109 110 278 (accept_3_2 109 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 278 2 54 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 278 (Polychromatic418967fa.accept_13_3_6_5_1_2336 107 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 278 2 53 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 105 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 278 2 52 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 278 (accept_3_2 103 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 278 2 51 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 278 (Polychromatic418967fa.accept_13_10_6_5_1_2297 101 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 278 2 50 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 278
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 99 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 278 2 49 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 278 (accept_3_2 97 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 278 2 48 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 110 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 278 2 47 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 93 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 278 2 46 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 278 (accept_3_2 91 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 278 2 45 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 278 (Polychromatic418967fa.accept_13_11_6_5_1_2339 89 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 278 2 44 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 278 2 43 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 278 (accept_3_2 85 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 278 2 42 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 278 (Polychromatic418967fa.accept_17_15_8_6_1_8733 83 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 278 2 41 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 278
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 81 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 278 2 40 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 278 (accept_3_2 79 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 278 2 39 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 278 2 38 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 278 2 37 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 278 (accept_3_2 73 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 278 2 36 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 278 (Polychromatic418967fa.accept_15_11_5_8_1_3157 71 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 278 2 35 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 278 2 34 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 278 (accept_3_2 67 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 278 2 33 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 278 (Polychromatic418967fa.accept_17_14_8_6_1_2643 65 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 278 2 32 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 278
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 278 2 31 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 278 (accept_3_2 61 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 278 2 30 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 278 2 29 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 278 2 28 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 278 (accept_3_2 55 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 278 2 27 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 278 (Polychromatic418967fa.accept_13_1_6_5_1_1610 53 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 278 2 26 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 278 2 25 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 278 (accept_3_2 49 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 278 2 24 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 278 (Polychromatic418967fa.accept_20_7_10_18_1_10001 47 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 278 2 23 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 278
  (Polychromatic418967fa.accept_19_7_15_12_1_4800 45 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 278 2 22 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 278 (accept_3_2 43 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 278 2 21 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 278 2 20 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 278 2 19 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 278 (accept_3_2 37 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 278 2 18 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 278 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 278 2 17 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 278 2 16 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 278 (accept_3_2 31 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 278 2 15 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 278 (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 278 2 14 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 278
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 278 2 13 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 278 (accept_3_2 25 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 278 2 12 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 278 2 11 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 278 2 10 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 278 (accept_3_2 19 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 278 2 9 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 278 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 278 2 8 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 278 2 7 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 278 (accept_3_2 13 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 278 2 6 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 278 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 278 2 5 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 278
  (Polychromatic418967fa.accept_17_9_8_6_1_6050 9 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 278 2 4 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 278 (accept_3_2 7 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  278 2 3 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 278 2 2 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 110 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 278 2 1 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 278 (accept_3_2 1 110 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 278 (allA_of_3_0 109 109 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 278
  (allA_succ_of_accept 107 108 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 107 108 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 278 2 53 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103
  105 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 278 2 52 54 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 278
  (accept_3_2 103 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 108 278 2 51 54 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 108 278
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 101 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 108 278 2 50 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 108 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 278 2 49 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 278 (accept_3_2 97 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 108 278 2 48 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 108 278
  (Polychromatic418967fa.accept_15_5_3_8_1_748 95 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 278 2 47 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 278 2 46 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 278 (accept_3_2 91 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 108 278 2 45 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 108 278
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 89 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 108 278 2 44 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 108 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 87 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 278 2 43 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 278 (accept_3_2 85 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 108 278 2 42 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 108 278
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 83 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 278 2 41 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 278 (Polychromatic418967fa.accept_19_5_13_12_1_13154 81 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 278 2 40 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 278 (accept_3_2 79 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 108 278 2 39 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 108 278
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 77 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 278 2 38 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 278 (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 278 2 37 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 278 (accept_3_2 73 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 108 278 2 36 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 108 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 278 2 35 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 69 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 278 2 34 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 278 (accept_3_2 67 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 108 278 2 33 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 108 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 278 2 32 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 278 (Polychromatic418967fa.accept_19_6_13_12_1_6220 63 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 278 2 31 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 278 (accept_3_2 61 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 278 2 30 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 278
  (Polychromatic418967fa.accept_25_9_8_3_1_17051 59 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 278 2 29 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 278 2 28 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 278 (accept_3_2 55 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 278 2 27 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 278 (Polychromatic418967fa.accept_13_1_4_5_1_113
  53 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 278 2 26 54 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 278 2 25 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 278 (accept_3_2 49 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 278 2 24 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 278 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 278 2 23 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 278
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 278 2 22 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 278 (accept_3_2 43 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 278 2 21 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 278 (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 278 2 20 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 278
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 278 2 19 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 278 (accept_3_2 37 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 278 2 18 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 278 2 17 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 278
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 33 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 108 278 2 16 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 108 278 (accept_3_2 31 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 278 2 15 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 278 2 14 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 278
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 278 2 13 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 278 (accept_3_2 25 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 278 2 12 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 278 2 11 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 278
  (Polychromatic418967fa.accept_20_1_8_18_1_8648 21 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 278 2 10 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 278 (accept_3_2 19 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 278 2 9 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 278 2 8 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 108 278 2 7 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 108 278 (accept_3_2 13 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 278 2 6 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 108 278 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 278 2 5 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 278 2 4 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 278 (accept_3_2 7 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108
  278 2 3 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 278 (Polychromatic418967fa.accept_14_5_10_12_1_1454 5 108 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 278 2 2 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 278 (Polychromatic418967fa.accept_19_3_13_12_1_10525 3 108 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 278 2 1 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 278 (accept_3_2 1 108 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 278 (allA_succ_of_accept 106 107 278 (accept_3_2 106 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 104 107
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 278 (accept_3_2 103 107
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 102 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 278 (accept_3_2 100 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 278 (Polychromatic418967fa.accept_16_2_11_6_1_737
  98 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 278 (accept_3_2 97
  107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 278
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 96 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 95 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 278 (accept_3_2 94 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 278 (accept_3_2 91 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 278 (Polychromatic418967fa.accept_20_10_7_18_1_11564 90 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 278 (accept_3_2 88 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 278
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 86 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 278 (accept_3_2 85 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 278 (Polychromatic418967fa.accept_13_6_3_5_1_3167 84 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 83 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 278 (accept_3_2 82 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 278 (accept_3_2 79 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 278 (Polychromatic418967fa.accept_27_24_26_8_1_17050 78 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 278 (accept_3_2 76 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 278 (accept_3_2 73 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 278 (accept_3_2 70 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 278 (accept_3_2 67 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 278 (accept_3_2 64 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 278
  (Polychromatic418967fa.accept_17_11_5_6_1_4928 62 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 278 (accept_3_2 61 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 278 (accept_3_2 58 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 278 (accept_3_2 55 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 278 (accept_3_2 52 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 278
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 278 (accept_3_2 49 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 278 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 278 (accept_3_2 46 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 278 (accept_3_2 43 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 278 (Polychromatic418967fa.accept_20_2_7_18_1_4145 42 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 278 (accept_3_2 40 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 278 (accept_3_2 37 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 278 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 278 (accept_3_2 34 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 278 (accept_3_2 31 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 278 (Polychromatic418967fa.accept_20_10_7_18_1_11564 30 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 278 (accept_3_2 28 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 278
  (Polychromatic418967fa.accept_29_26_20_17_1_17049 26 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 107 278 (accept_3_2 25 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 107 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 278 (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 107
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 278 (accept_3_2 22 107
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3
  21 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 278 (accept_3_2 19 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 278 (accept_3_2 16 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 278
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 278 (accept_3_2 13 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 278 (Polychromatic418967fa.accept_25_12_7_3_1_17048 12 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 278 (accept_3_2 10 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 278 (accept_3_2 7 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 278 (accept_3_2 4 107 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 278
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 278 (accept_3_2 1 107 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 278 (allA_of_3_0 106 106 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 278
  (allA_succ_of_accept 104 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 105 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 278 (accept_3_2 103 105 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 278 (accept_3_2 100 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 278 (Polychromatic418967fa.accept_16_2_9_6_1_4441 98 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 278 (accept_3_2 97 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 278 (Polychromatic418967fa.accept_11_8_6_3_1_661 96 105
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 278 (accept_3_2 94 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 278 (accept_3_2 91 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 278 (accept_3_2 88 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 278 (accept_3_2 85 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 278 (accept_3_2 82 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 278 (Polychromatic418967fa.accept_13_3_1_5_1_499 81 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 278 (Polychromatic418967fa.accept_23_11_13_2_1_17047 80 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 278 (accept_3_2 79 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 105
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 278 (accept_3_2 76 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 278 (accept_3_2 73 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 278 (accept_3_2 70 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 278 (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 278 (accept_3_2 67 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 278 (accept_3_2 64 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 278 (accept_3_2 61 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 278 (Polychromatic418967fa.accept_13_8_1_5_1_3176 60 105
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 278 (accept_3_2 58 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 278 (accept_3_2 55 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 278 (accept_3_2 52 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 278 (accept_3_2 49 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 278 (accept_3_2 46 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 278 (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 278 (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 278 (accept_3_2 43 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 278 (accept_3_2 40 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 278 (accept_3_2 37 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 278 (Polychromatic418967fa.accept_19_17_10_12_1_6157 36 105 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 278 (accept_3_2 34 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 278 (accept_3_2 31 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 278 (accept_3_2 28 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 278 (Polychromatic418967fa.accept_17_9_3_6_1_11232 26 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 278 (accept_3_2 25 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 278 (Polychromatic418967fa.accept_28_24_21_26_1_13239 24
  105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 278 (accept_3_2 22 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 278 (accept_3_2 19 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 278 (accept_3_2 16 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 278 (accept_3_2 13 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 278 (accept_3_2 10 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 278 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 278 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 278 (accept_3_2 7 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 278 (accept_3_2 4 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 278 (accept_3_2 1 105 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 278 (allA_succ_of_accept 103 104 278 (accept_3_2 103 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 278 2 51 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 278 2 50 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 99 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 278 2 49 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 278 (accept_3_2 97 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 278 2 48 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 278 2 47 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 93 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 278 2 46 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 278 (accept_3_2 91 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 278 2 45 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 89 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 278 2 44 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 278 2 43 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 278 (accept_3_2 85 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 278 2 42 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 278 2 41 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 278 2 40 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 278 (accept_3_2 79 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 278 2 39 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 278 2 38 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 278 2 37 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 278 (accept_3_2 73 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 278 2 36 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 278 2 35 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 278 2 34 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 278 (accept_3_2 67 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 278 2 33 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 278 2 32 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 278 2 31 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 278 (accept_3_2 61 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 278 2 30 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 278 2 29 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 278 2 28 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 278 (accept_3_2 55 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 278 2 27 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 278 2 26 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 278 2 25 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 278 (accept_3_2 49 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 278 2 24 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 278 2 23 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 278
  (Polychromatic418967fa.accept_23_22_12_2_1_13872 45 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 104 278 2 22 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 104 278 (accept_3_2 43 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 278 2 21 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 278 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 278 2 20 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 278 2 19 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 278 (accept_3_2 37 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 278 2 18 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 104 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 278 2 17 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 278 2 16 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 278 (accept_3_2 31 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 278 2 15 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 278 2 14 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 278
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 278 2 13 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 278 (accept_3_2 25 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 278 2 12 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 104 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 278 2 11 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 278 2 10 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 278 (accept_3_2 19 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 278 2 9 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 104 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 278 2 8 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 278 2 7 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 104 278 (accept_3_2 13 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 278 2 6 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 104 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 278 2 5 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 278 2 4 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 278 (accept_3_2 7 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  278 2 3 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 278 2 2 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 104 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 104 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 278 2 1 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 278 (accept_3_2 1 104 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 278 (allA_of_3_0 103 103 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 278 (allA_succ_of_accept 101
  102 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 278 2 50 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 278 2 49 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 278 (accept_3_2 97 102 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 278 2 48 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 278 2 47 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 278 2 46 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 278 (accept_3_2 91 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 278 2 45 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 278
  (Polychromatic418967fa.accept_24_17_6_14_1_11994 89 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 102 278 2 44 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 102 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 278 2 43 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 278 (accept_3_2 85 102 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 278 2 42 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 278 2 41 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 278 2 40 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 278 (accept_3_2 79 102 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 278 2 39 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 278 2 38 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 278 2 37 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 278 (accept_3_2 73 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 102 278 2 36 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 102 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 71
  102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 278 2 35 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 278 2 34 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 278 (accept_3_2 67 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 278 2 33 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 278 2 32 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 278 2 31 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 278 (accept_3_2 61 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 278 2 30 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 278 2 29 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 278 2 28 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 278 (accept_3_2 55 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 278 2 27 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 278 (Polychromatic418967fa.accept_19_15_7_12_1_11763 53 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 278 2 26 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 278 2 25 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 278 (accept_3_2 49 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 278 2 24 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 278 2 23 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 278 2 22 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 278 (accept_3_2 43 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 278 2 21 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 278 2 20 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 278 2 19 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 278 (accept_3_2 37 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 278 2 18 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 278 2 17 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 278 2 16 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 278 (accept_3_2 31 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 278 2 15 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 278 2 14 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 278 2 13 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 278 (accept_3_2 25 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 278 2 12 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 278 2 11 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 278 2 10 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 278 (accept_3_2 19 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 278 2 9 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 278 (Polychromatic418967fa.accept_20_17_2_18_1_11576 17 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 278 2 8 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 278 2 7 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 278 (accept_3_2 13 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 278 2 6 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 278 2 5 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 278 2 4 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 278 (accept_3_2 7 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  278 2 3 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 278 2 2 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 102 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 278 2 1 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 278 (accept_3_2 1 102 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 278 (allA_succ_of_accept 100 101 278 (accept_3_2 100 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 278 (Polychromatic418967fa.accept_21_14_17_5_1_3459 98 101
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 278 (accept_3_2 97 101
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 278 (accept_3_2 94 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 92
  101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 278 (accept_3_2 91
  101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 278
  (Polychromatic418967fa.accept_19_14_6_12_1_13167 90 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 278 (Polychromatic418967fa.accept_10_9_1_8_1_755 89 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 278 (accept_3_2 88 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 86 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 278 (accept_3_2 85 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 278 (accept_3_2 82 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 80 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 278 (accept_3_2 79 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 278 (accept_3_2 76 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 278
  (Polychromatic418967fa.accept_19_17_6_12_1_7757 74 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 101 278 (accept_3_2 73 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 101 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 278 (accept_3_2 70 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69
  101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 278 (accept_3_2 67 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 278 (accept_3_2 64 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 278
  (Polychromatic418967fa.accept_22_18_13_14_1_4469 62 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 101 278 (accept_3_2 61 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 101 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 278 (accept_3_2 58 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57
  101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 56 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 278 (accept_3_2 55 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 278 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 278 (accept_3_2 52 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 278 (accept_3_2 49 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 278 (accept_3_2 46 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 278 (accept_3_2 43 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 278 (accept_3_2 40 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 278
  (Polychromatic418967fa.accept_22_16_13_14_1_14009 38 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 278 (accept_3_2 37 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 278 (accept_3_2 34 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 278 (accept_3_2 31 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 278 (accept_3_2 28 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 278
  (Polychromatic418967fa.accept_17_9_16_6_1_4820 26 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 278 (accept_3_2 25 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 278 (accept_3_2 22 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 278 (accept_3_2 19 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 278 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 278 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 278 (accept_3_2 16 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 278 (accept_3_2 13 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 278 (accept_3_2 10 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 278 (accept_3_2 7 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 278 (accept_3_2 4 101 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 278 (accept_3_2 1 101 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 278 (allA_of_3_0 100 100 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 278 (allA_succ_of_accept 98 99
  278 (Polychromatic418967fa.accept_16_2_3_6_1_3372 98 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 278 (accept_3_2 97 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 278 (Polychromatic418967fa.accept_18_6_9_8_1_6812 96 99 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 278 (accept_3_2 94 99 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 93
  99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 278
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 92 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 278 (accept_3_2 91 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 278 (accept_3_2 88 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 278
  (Polychromatic418967fa.accept_22_20_11_14_1_13985 86 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 99 278 (accept_3_2 85 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 99 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 99 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 278 (accept_3_2 82 99 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81
  99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 278 (accept_3_2 79 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 278 (accept_3_2 76 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 278 (Polychromatic418967fa.accept_13_10_8_5_1_1616 75 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 278 (accept_3_2 73 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 278 (Polychromatic418967fa.accept_21_9_15_5_1_3500 72 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 278 (accept_3_2 70 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 278
  (Polychromatic418967fa.accept_13_3_8_5_1_974 68 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 278 (accept_3_2 67 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 278 (accept_3_2 64 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 278 (accept_3_2 61 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 278 (accept_3_2 58 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 278
  (Polychromatic418967fa.accept_21_14_15_5_1_6553 56 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 278 (accept_3_2 55 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 278 (accept_3_2 52 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 278 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 278
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 50 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 278 (accept_3_2 49 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 278 (accept_3_2 46 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 278 (accept_3_2 43 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 278 (accept_3_2 40 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 278 (accept_3_2 37 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 278 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 278 (accept_3_2 34 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 278 (accept_3_2 31 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 278 (accept_3_2 28 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 278
  (Polychromatic418967fa.accept_19_7_4_12_1_4769 26 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 278 (accept_3_2 25 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 278 (accept_3_2 22 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 278 (accept_3_2 19 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 278 (accept_3_2 16 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 278 (Polychromatic418967fa.accept_17_15_14_6_1_7354 15 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 278 (accept_3_2 13 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 278 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 278 (accept_3_2 10 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 278
  (Polychromatic418967fa.accept_17_8_14_6_1_8727 8 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 278 (accept_3_2 7 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 278 (accept_3_2 4 99 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 278 (Polychromatic418967fa.accept_15_2_9_8_1_736 2
  99 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 278 (accept_3_2 1 99 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  278 (allA_succ_of_accept 97 98 278 (accept_3_2 97 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 278 2 48 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 278 (Polychromatic418967fa.accept_11_7_10_3_1_633 95 98 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 278 2 47 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 278 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  93 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 278 2 46 49 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 278
  (accept_3_2 91 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 278 2 45 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 278
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 89 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 278 2 44 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 278 (Polychromatic418967fa.accept_17_2_13_6_1_3772 87 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 278 2 43 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 278 (accept_3_2 85 98 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 278 2 42 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 278 (Polychromatic418967fa.accept_16_3_2_6_1_4461
  83 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 278 2 41 49 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 278
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 81 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 278 2 40 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 278 (accept_3_2 79 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 278 2 39 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 278 (Polychromatic418967fa.accept_13_12_7_5_1_3147 77 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 278 2 38 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 278
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 75 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 278 2 37 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 278 (accept_3_2 73 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 278 2 36 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 278 (Polychromatic418967fa.accept_21_8_14_5_1_8177 71 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 278 2 35 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 278
  (Polychromatic418967fa.accept_25_19_23_3_1_15455 69 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 98 278 2 34 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 98 278 (accept_3_2 67 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 278 2 33 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 278 (Polychromatic418967fa.accept_16_1_2_6_1_2295 65 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 278 2 32 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 278
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 278 2 31 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 278 (accept_3_2 61 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 278 2 30 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 278 (Polychromatic418967fa.accept_16_11_2_6_1_1435 59 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 278 2 29 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 278
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 57 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 278 2 28 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 278 (accept_3_2 55 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 278 2 27 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 278 (Polychromatic418967fa.accept_17_2_13_6_1_3772 53 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 278 2 26 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 278
  (Polychromatic418967fa.accept_11_7_10_3_1_633 51 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 278 2 25 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 278 (accept_3_2 49 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 278 2 24 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 278 (Polychromatic418967fa.accept_19_9_3_12_1_6191 47 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 278 2 23 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 278
  (Polychromatic418967fa.accept_17_11_13_6_1_2625 45 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 278 2 22 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 278 (accept_3_2 43 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 278 2 21 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 278 (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 278 2 20 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 278
  (Polychromatic418967fa.accept_21_18_14_5_1_8193 39 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 278 2 19 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 278 (accept_3_2 37 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 278 2 18 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 278 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 278 2 17 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 278
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 278 2 16 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 278 (accept_3_2 31 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 278 2 15 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 278 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 278 2 14 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 278
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 278 2 13 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 278 (accept_3_2 25 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 278 2 12 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 278 (Polychromatic418967fa.accept_22_1_10_14_1_10991 23 98 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 278 2 11 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 278
  (Polychromatic418967fa.accept_19_2_3_12_1_10559 21 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 278 2 10 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 278 (accept_3_2 19 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 278 2 9 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 278 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 98 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 278 2 8 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 278 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  15 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 278 2 7 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 278 (accept_3_2 13
  98 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 278 2 6 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 278
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 278 2 5 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 278 (Polychromatic418967fa.accept_16_9_2_6_1_4434 9 98 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 278 2 4 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 278 (accept_3_2 7 98 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 278 2 3 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 278 (Polychromatic418967fa.accept_25_5_23_3_1_17046 5 98 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 278 2 2 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 278 (Polychromatic418967fa.accept_16_3_2_6_1_4461 3
  98 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 278 2 1 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 278 (accept_3_2 1 98
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  278 (allA_of_3_0 97 97 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 278 (allA_succ_of_accept 95 96 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 278 2 47 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 278 2 46 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 278 (accept_3_2 91 96 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 278 2 45 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 278 (Polychromatic418967fa.accept_15_14_6_8_1_1410
  89 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 278 2 44 48 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 278
  (Polychromatic418967fa.accept_19_11_1_12_1_6237 87 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 278 2 43 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 278 (accept_3_2 85 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 278 2 42 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 96 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 278 2 41 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 278
  (Polychromatic418967fa.accept_17_13_11_6_1_4837 81 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 96 278 2 40 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 96 278 (accept_3_2 79 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 278 2 39 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 278 2 38 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 278 2 37 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 278 (accept_3_2 73 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 278 2 36 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 96 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 278 2 35 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 278
  (Polychromatic418967fa.accept_21_6_12_5_1_6593 69 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 278 2 34 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 96 278 (accept_3_2 67 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 278 2 33 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 278 2 32 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 278 2 31 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 96 278 (accept_3_2 61 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 278 2 30 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 278 2 29 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 278 2 28 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 278 (accept_3_2 55 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 278 2 27 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 278 2 26 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 278
  (Polychromatic418967fa.accept_19_13_1_12_1_11768 51 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 96 278 2 25 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 96 278 (accept_3_2 49 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 278 2 24 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 278 2 23 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 278
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 278 2 22 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 96 278 (accept_3_2 43 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 278 2 21 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 278 2 20 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 278 2 19 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 278 (accept_3_2 37 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 278 2 18 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 278 (Polychromatic418967fa.accept_20_15_16_18_1_5597 35 96 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 278 2 17 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 278 2 16 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 278 (accept_3_2 31 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 278 2 15 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 278 2 14 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 278
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 278 2 13 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 96 278 (accept_3_2 25 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 278 2 12 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 278 2 11 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 278 2 10 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 278 (accept_3_2 19 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 278 2 9 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 96 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 278 2 8 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 278
  (Polychromatic418967fa.accept_20_15_16_18_1_5597 15 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 278 2 7 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 96 278 (accept_3_2 13 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 278 2 6 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 278 2 5 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 278 (Polychromatic418967fa.accept_18_9_6_8_1_2989 9
  96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 278 2 4 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 278 (accept_3_2 7 96
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 278 2 3 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 278 2 2 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 278 2 1 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 278 (accept_3_2 1 96 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 278
  (allA_succ_of_accept 94 95 278 (accept_3_2 94 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 278 (accept_3_2 91 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 278 (accept_3_2 88 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 278 (accept_3_2 85 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 278 (accept_3_2 82 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 278 (accept_3_2 79 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 95 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 278 (accept_3_2 76 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 278 (accept_3_2 73 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 278 (accept_3_2 70 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 278 (accept_3_2 67 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 95 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 278 (accept_3_2 64 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 278 (accept_3_2 61 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 278
  (Polychromatic418967fa.accept_11_4_7_3_1_289 59 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 278 (accept_3_2 58 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 278 (accept_3_2 55 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 278 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 278 (accept_3_2 52 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 278 (accept_3_2 49 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 278 (accept_3_2 46 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 278 (accept_3_2 43 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 278 (accept_3_2 40 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 278 (accept_3_2 37 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 278
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 278 (accept_3_2 34 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 278 (accept_3_2 31 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 278 (accept_3_2 28 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 278 (accept_3_2 25 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 278 (accept_3_2 22 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 278 (accept_3_2 19 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 278 (accept_3_2 16 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 278 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 278 (accept_3_2 13 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 278 (accept_3_2 10 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 278 (accept_3_2 7 95 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 278 (accept_3_2 4 95 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 278 (accept_3_2 1 95 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 278
  (allA_of_3_0 94 94 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 278 (allA_succ_of_accept 92 93 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 278 (accept_3_2 91 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 278 (accept_3_2 88 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 278 (accept_3_2 85 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 84 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 278 (accept_3_2 82 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 278 (accept_3_2 79 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 278 (accept_3_2 76 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 278 (accept_3_2 73 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 278 (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 278 (accept_3_2 70 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 278 (accept_3_2 67 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 278 (accept_3_2 64 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 278
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 62 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 278 (accept_3_2 61 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 278 (accept_3_2 58 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 278 (Polychromatic418967fa.accept_15_12_3_8_1_5245 57 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 278 (accept_3_2 55 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 278 (accept_3_2 52 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 278 (accept_3_2 49 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 278 (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 278 (accept_3_2 46 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 278
  (Polychromatic418967fa.accept_19_6_17_12_1_10550 44 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 93 278 (accept_3_2 43 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 93 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 278 (accept_3_2 40 93 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 278 (accept_3_2 37 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 278 (accept_3_2 34 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 278 (accept_3_2 31 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 278 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 278 (accept_3_2 28 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 278 (accept_3_2 25 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 278 (accept_3_2 22 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 278 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 278 (accept_3_2 19 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 278 (accept_3_2 16 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 278 (accept_3_2 13 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 278 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 278 (accept_3_2 10 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 278 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 93 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 278 (accept_3_2 7 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 278 (accept_3_2 4 93 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 278 (accept_3_2 1 93 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 278
  (allA_succ_of_accept 91 92 278 (accept_3_2 91 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  278 2 45 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 278 2 44 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 92 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 278 2 43 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 278 (accept_3_2 85 92 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 278 2 42 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 278 2 41 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 278 2 40 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 278 (accept_3_2 79 92 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 278 2 39 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 77
  92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 278 2 38 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 278 2 37 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 278 (accept_3_2 73 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 278 2 36 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 92 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 278 2 35 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 278 2 34 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 92 278 (accept_3_2 67 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 92 278 2 33 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 92 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 92 278 2 32 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 92 278
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 63 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 92 278 2 31 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 92 278 (accept_3_2 61 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 92 278 2 30 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 92 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 278 2 29 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 278 2 28 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 92 278 (accept_3_2 55 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 92 278 2 27 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 92 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 278 2 26 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 278 2 25 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 92 278 (accept_3_2 49 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 278 2 24 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 92 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 278 2 23 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 92 278 2 22 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 92 278 (accept_3_2 43 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 92 278 2 21 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 92 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 278 2 20 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 278 2 19 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 278 (accept_3_2 37 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 278 2 18 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 92 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 278 2 17 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 278 2 16 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 92 278 (accept_3_2 31 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 278 2 15 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 92 278 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 278 2 14 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 278 2 13 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 92 278 (accept_3_2 25 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 278 2 12 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 92 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 278 2 11 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 278 2 10 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 92 278 (accept_3_2 19 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 92 278 2 9 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 92 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 278 2 8 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 278 2 7 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 278 (accept_3_2 13
  92 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 278 2 6 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 92 278 2 5 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 278 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 92 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 278 2 4 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 278 (accept_3_2 7 92 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 278 2 3 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 278 2 2 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 278 2 1 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 278 (accept_3_2 1 92
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 278
  (allA_of_3_0 91 91 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 278 (allA_succ_of_accept 89 90 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 89 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 278 2 44 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 87 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 278 2 43 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 278 (accept_3_2 85 90 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 278 2 42 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 278 (Polychromatic418967fa.accept_14_13_6_12_1_3126
  83 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 278 2 41 45 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 278 2 40 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 278 (accept_3_2 79 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 278 2 39 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 278 (Polychromatic418967fa.accept_20_17_10_18_1_4150 77 90 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 278 2 38 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 278 2 37 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 278 (accept_3_2 73 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 278 2 36 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 278 2 35 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 278 2 34 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 278 (accept_3_2 67 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 278 2 33 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 278 (Polychromatic418967fa.accept_20_5_10_18_1_5622 65 90 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 278 2 32 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 278 2 31 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 278 (accept_3_2 61 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 278 2 30 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 278 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 278 2 29 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 278 2 28 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 278 (accept_3_2 55 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 278 2 27 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 278 2 26 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 278 2 25 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 278 (accept_3_2 49 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 278 2 24 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 278 (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 278 2 23 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 278 2 22 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 278 (accept_3_2 43 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 278 2 21 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 278 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 278 2 20 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 278 2 19 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 278 (accept_3_2 37 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 278 2 18 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 278 (Polychromatic418967fa.accept_17_1_5_6_1_3717 35 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 278 2 17 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 278 2 16 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 278 (accept_3_2 31 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 278 2 15 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 278 2 14 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 278 2 13 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 278 (accept_3_2 25 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 278 2 12 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 278 2 11 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 278 2 10 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 278 (accept_3_2 19 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 278 2 9 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 278 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 90 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 278 2 8 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 278 2 7 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 278 (accept_3_2 13
  90 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 278 2 6 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 278 2 5 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 278 2 4 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 278 (accept_3_2 7 90 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 278 2 3 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 278 (Polychromatic418967fa.accept_20_5_10_18_1_5622 5 90 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 278 2 2 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  90 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 278 2 1 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 278 (accept_3_2 1 90
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 278
  (allA_succ_of_accept 88 89 278 (accept_3_2 88 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 278 (Polychromatic418967fa.accept_22_20_1_14_1_9367 86 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 278 (accept_3_2 85 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 89 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 278 (accept_3_2 82 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 80 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 278 (accept_3_2 79 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 278 (Polychromatic418967fa.accept_17_10_4_6_1_3757 78 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 278
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 278 (accept_3_2 76 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 278 (accept_3_2 73 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 278 (Polychromatic418967fa.accept_13_7_11_5_1_2302 72 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 278 (accept_3_2 70 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 68 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 278 (accept_3_2 67 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 66 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 278
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 278 (accept_3_2 64 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 278 (Polychromatic418967fa.accept_17_11_4_6_1_2631 62 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 278 (accept_3_2 61 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 278 (Polychromatic418967fa.accept_19_3_13_12_1_10525 60 89
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 278 (accept_3_2 58 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 278 (accept_3_2 55 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 278
  (Polychromatic418967fa.accept_17_2_4_6_1_1619 53 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 278 (accept_3_2 52 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 50 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 278 (accept_3_2 49 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 278 (Polychromatic418967fa.accept_25_23_14_3_1_8295 48 89
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 278 (accept_3_2 46 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 278 (accept_3_2 43 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 278 (Polychromatic418967fa.accept_13_3_11_5_1_2348 42 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 278
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 278 (accept_3_2 40 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 278 (Polychromatic418967fa.accept_14_10_5_12_1_3995 38 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 278 (accept_3_2 37 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 278 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 89 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 278 (accept_3_2 34 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 278 (accept_3_2 31 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 278 (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 89 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 278
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 278 (accept_3_2 28 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 278 (Polychromatic418967fa.accept_23_3_20_2_1_15603 26 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 278 (accept_3_2 25 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 89 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 278 (accept_3_2 22 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 278 (accept_3_2 19 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 278 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 278
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 278 (accept_3_2 16 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 278 (accept_3_2 13 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 278 (Polychromatic418967fa.accept_28_12_5_26_1_17045 12 89 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 278 (accept_3_2 10 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 278 (accept_3_2 7 89 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 278 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 89 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 278
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 278 (accept_3_2 4 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 89 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 278 (accept_3_2 1 89 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 278 (allA_of_3_0 88 88 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 278
  (allA_succ_of_accept 86 87 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 87 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 278 (accept_3_2 85 87 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 278 (accept_3_2 82 87
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 278
  (Polychromatic418967fa.accept_13_2_9_5_1_959 80 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 278 (accept_3_2 79 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 278 (accept_3_2 76 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 278 (accept_3_2 73 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 278 (accept_3_2 70 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 278 (accept_3_2 67 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 278 (accept_3_2 64 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 278
  (Polychromatic418967fa.accept_11_7_10_3_1_633 62 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 278 (accept_3_2 61 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 278 (Polychromatic418967fa.accept_19_3_11_12_1_9102 60 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 278 (accept_3_2 58 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 278 (accept_3_2 55 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 278 (accept_3_2 52 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 278 (accept_3_2 49 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 278 (accept_3_2 46 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 278 (accept_3_2 43 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 278 (accept_3_2 40 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 278 (accept_3_2 37 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 278 (accept_3_2 34 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 278 (accept_3_2 31 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 278 (accept_3_2 28 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 278 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 278
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 278 (accept_3_2 25 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 278 (Polychromatic418967fa.accept_19_5_11_12_1_11765 24 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 278 (accept_3_2 22 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 278 (accept_3_2 19 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 278 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 278 (accept_3_2 16 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 278 (accept_3_2 13 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 278 (accept_3_2 10 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 278 (accept_3_2 7 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  278 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 278 (accept_3_2 4 87 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 278 (accept_3_2 1 87 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 278
  (allA_succ_of_accept 85 86 278 (accept_3_2 85 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  278 2 42 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 278 2 41 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 86 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 278 2 40 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 278 (accept_3_2 79 86 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 278 2 39 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 278
  (Polychromatic418967fa.accept_13_12_8_5_1_976 77 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 278 2 38 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 278 2 37 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 278 (accept_3_2 73 86 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 278 2 36 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 278 (Polychromatic418967fa.accept_17_3_1_6_1_251 71
  86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 278 2 35 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 278 2 34 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 278 (accept_3_2 67 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 278 2 33 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 278 2 32 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 278 2 31 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 278 (accept_3_2 61 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 278 2 30 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 278 2 29 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 278 2 28 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 278 (accept_3_2 55 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 278 2 27 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 278 2 26 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 278 2 25 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 278 (accept_3_2 49 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 278 2 24 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 278 2 23 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 278 2 22 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 278 (accept_3_2 43 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 278 2 21 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 278 2 20 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 278 2 19 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 278 (accept_3_2 37 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 278 2 18 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 278 (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 278 2 17 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 278 2 16 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 278 (accept_3_2 31 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 278 2 15 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 278 2 14 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 278
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 278 2 13 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 278 (accept_3_2 25 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 278 2 12 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 278 2 11 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 278 2 10 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 278 (accept_3_2 19 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 278 2 9 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 278 2 8 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 278 2 7 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 278 (accept_3_2 13
  86 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 278 2 6 43 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 86 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 278 2 5 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 278 (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 86 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 278 2 4 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 278 (accept_3_2 7 86 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 278 2 3 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 278 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 86 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 278 2 2 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 278 2 1 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 278 (accept_3_2 1 86
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 278
  (allA_of_3_0 85 85 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 278 (allA_succ_of_accept 83 84 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 278 2 41 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 278 2 40 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 278 (accept_3_2 79 84 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 278 2 39 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 77
  84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 278 2 38 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 278
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 278 2 37 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 278 (accept_3_2 73 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 278 2 36 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 84 278 (Polychromatic418967fa.accept_32_7_20_22_1_12619 71 84 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 278 2 35 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 84 278 2 34 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 84 278 (accept_3_2 67 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 278 2 33 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 278 2 32 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 84 278
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 84 278 2 31 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 278 (accept_3_2 61 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 278 2 30 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 278 2 29 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 278
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 57 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 278 2 28 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 84 278 (accept_3_2 55 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 278 2 27 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 278 (Polychromatic418967fa.accept_13_1_6_5_1_1610 53 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 278 2 26 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 278 2 25 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 84 278 (accept_3_2 49 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 278 2 24 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 278 2 23 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 278
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 278 2 22 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 84 278 (accept_3_2 43 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 278 2 21 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 278 2 20 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 278 2 19 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 278 (accept_3_2 37 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 278 2 18 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 278 (Polychromatic418967fa.accept_16_3_4_6_1_6798 35 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 278 2 17 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 278 2 16 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 278 (accept_3_2 31 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 278 2 15 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 278 2 14 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 278
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 278 2 13 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 84 278 (accept_3_2 25 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 278 2 12 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 278 2 11 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 278
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 278 2 10 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 278 (accept_3_2 19 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 278 2 9 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 278 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 84 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 278 2 8 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 278 2 7 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 278 (accept_3_2 13
  84 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 278 2 6 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 278 2 5 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 84 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 278 2 4 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 278 (accept_3_2 7 84 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 84 278 2 3 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 84 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 278 2 2 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 278 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3
  84 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 278 2 1 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 278 (accept_3_2 1 84
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 278
  (allA_succ_of_accept 82 83 278 (accept_3_2 82 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 278 (accept_3_2 79 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 278 (accept_3_2 76 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 278 (accept_3_2 73 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 278 (Polychromatic418967fa.accept_19_15_7_12_1_11763 72 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 278 (accept_3_2 70 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 278 (accept_3_2 67 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 278 (accept_3_2 64 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 278 (Polychromatic418967fa.accept_14_6_13_12_1_810 62 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 278 (accept_3_2 61 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 278 (accept_3_2 58 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 278 (accept_3_2 55 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 278 (Polychromatic418967fa.accept_19_16_7_12_1_6252 54 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 278 (accept_3_2 52 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 278 (accept_3_2 49 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 278
  (Polychromatic418967fa.accept_22_3_17_14_1_17044 47 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 83 278 (accept_3_2 46 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 83
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 278 (accept_3_2 43 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42
  83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 278 (accept_3_2 40 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 278 (Polychromatic418967fa.accept_25_13_8_3_1_17043 38 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 278 (accept_3_2 37 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 278
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 278 (accept_3_2 34 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 278 (accept_3_2 31 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 278 (accept_3_2 28 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 278 (accept_3_2 25 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 278 (accept_3_2 22 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 278 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 278 (accept_3_2 19 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 278 (accept_3_2 16 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 278 (accept_3_2 13 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 278 (accept_3_2 10 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 278 (accept_3_2 7 83 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 278 (accept_3_2 4 83 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 278
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 278 (accept_3_2 1 83 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 278 (allA_of_3_0
  82 82 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 278 (allA_succ_of_accept 80 81 278
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 80 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 278 (accept_3_2 79 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 278 (accept_3_2 76 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 278
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 74 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 278 (accept_3_2 73 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 278 (accept_3_2 70 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 278
  (Polychromatic418967fa.accept_19_11_5_12_1_3439 68 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 278 (accept_3_2 67 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 278 (accept_3_2 64 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 278 (accept_3_2 61 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 278 (accept_3_2 58 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 278
  (Polychromatic418967fa.accept_20_16_1_18_1_5617 56 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 278 (accept_3_2 55 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 278 (accept_3_2 52 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 278 (accept_3_2 49 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 278 (accept_3_2 46 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 278 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 278 (accept_3_2 43 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 278 (accept_3_2 40 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 278
  (Polychromatic418967fa.accept_25_13_6_3_1_15424 38 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 278 (accept_3_2 37 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 278 (accept_3_2 34 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 278
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 278 (accept_3_2 31 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 278 (accept_3_2 28 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 278
  (Polychromatic418967fa.accept_19_7_5_12_1_7756 26 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 278 (accept_3_2 25 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 278 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 278 (accept_3_2 22 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 278 (accept_3_2 19 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 278 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 278 (accept_3_2 16 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 278
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 278 (accept_3_2 13 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 278 (Polychromatic418967fa.accept_21_12_18_5_1_14149 12 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 278 (accept_3_2 10 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 278 (accept_3_2 7 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 278 (accept_3_2 4 81 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  81 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 278 (accept_3_2 1 81 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 278
  (allA_succ_of_accept 79 80 278 (accept_3_2 79 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  278 2 39 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 278 2 38 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 278 (Polychromatic418967fa.accept_13_10_2_5_1_1633 75 80 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 278 2 37 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 278 (accept_3_2 73 80 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 278 2 36 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 278 2 35 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 80 278 (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 278 2 34 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 278 (accept_3_2 67 80 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 278 2 33 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 278 2 32 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 278
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 278 2 31 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 80 278 (accept_3_2 61 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 80 278 2 30 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 80 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 278 2 29 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 278 2 28 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 80 278 (accept_3_2 55 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 80 278 2 27 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 80 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 278 2 26 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 278 2 25 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 80 278 (accept_3_2 49 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 80 278 2 24 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 80 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 278 2 23 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 278
  (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 278 2 22 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 80 278 (accept_3_2 43 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 80 278 2 21 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 80 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 278 2 20 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 278
  (Polychromatic418967fa.accept_19_1_4_12_1_6275 39 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 278 2 19 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 278 (accept_3_2 37 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 278 2 18 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 80 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 278 2 17 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 278
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 278 2 16 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 80 278 (accept_3_2 31 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 80 278 2 15 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 80 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 278 2 14 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 278
  (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 278 2 13 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 80 278 (accept_3_2 25 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 80 278 2 12 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 80 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 278 2 11 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 278
  (Polychromatic418967fa.accept_19_2_4_12_1_13084 21 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 278 2 10 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 80 278 (accept_3_2 19 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 80 278 2 9 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 80 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 278 2 8 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 278 2 7 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 278 (accept_3_2 13
  80 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 278 2 6 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 278
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 278 2 5 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 278 2 4 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 278 (accept_3_2 7 80 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 278 2 3 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 80 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 80 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 278 2 2 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 278 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3
  80 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 278 2 1 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 278 (accept_3_2 1 80
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 278 (allA_of_3_0 79
  79 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 278 (allA_succ_of_accept 77 78 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 78 278 2 38 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 78 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 278 2 37 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 278 (accept_3_2 73 78 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 278 2 36 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 278 (Polychromatic418967fa.accept_15_11_3_8_1_750
  71 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 278 2 35 39 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 278 2 34 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 278 (accept_3_2 67 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 278 2 33 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 78 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 278 2 32 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 278 2 31 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 278 (accept_3_2 61 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 278 2 30 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 278 2 29 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 278 2 28 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 278 (accept_3_2 55 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 278 2 27 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 278 2 26 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 278 2 25 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 278 (accept_3_2 49 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 278 2 24 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 278 2 23 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 278 2 22 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 278 (accept_3_2 43 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 278 2 21 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 278 2 20 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 278 2 19 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 278 (accept_3_2 37 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 278 2 18 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 278 2 17 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 278 2 16 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 278 (accept_3_2 31 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 278 2 15 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 278 2 14 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 278 2 13 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 278 (accept_3_2 25 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 278 2 12 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 278 2 11 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 278 2 10 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 278 (accept_3_2 19 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 278 2 9 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 278 2 8 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 278 2 7 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 278 (accept_3_2 13
  78 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 278 2 6 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 278 2 5 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 78 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 278 2 4 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 278 (accept_3_2 7 78 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 278 2 3 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 278 2 2 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 278 2 1 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 278 (accept_3_2 1 78
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 278
  (allA_succ_of_accept 76 77 278 (accept_3_2 76 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 278 (accept_3_2 73 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 278 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 278 (accept_3_2 70 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 278 (accept_3_2 67 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 278 (accept_3_2 64 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 278 (Polychromatic418967fa.accept_19_5_1_12_1_6102 62 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 278 (accept_3_2 61 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 278 (accept_3_2 58 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 278 (accept_3_2 55 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 278 (Polychromatic418967fa.accept_13_2_12_5_1_1602 54 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 278
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 278 (accept_3_2 52 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 278 (Polychromatic418967fa.accept_17_16_9_6_1_3723 50 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 278 (accept_3_2 49 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 278 (accept_3_2 46 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 278 (accept_3_2 43 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 278
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 278 (accept_3_2 40 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 278 (accept_3_2 37 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 278 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 278 (accept_3_2 34 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 278 (accept_3_2 31 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 278 (accept_3_2 28 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 278 (Polychromatic418967fa.accept_19_7_1_12_1_6134 26 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 278 (accept_3_2 25 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 278 (accept_3_2 22 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 278 (accept_3_2 19 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 278 (Polychromatic418967fa.accept_19_18_1_12_1_6235 18 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 278
  (Polychromatic418967fa.accept_13_4_12_5_1_476 17 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 278 (accept_3_2 16 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 278 (accept_3_2 13 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 278 (accept_3_2 10 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 278 (accept_3_2 7 77 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 278
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 278 (accept_3_2 4 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 278 (accept_3_2 1 77 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 278 (allA_of_3_0 76 76 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 278 (allA_succ_of_accept 74 75
  278 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 278 (accept_3_2 73 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 278 (accept_3_2 70 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 278 (accept_3_2 67 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 278 (accept_3_2 64 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 278 (accept_3_2 61 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 278 (accept_3_2 58 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 278 (accept_3_2 55 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 278 (accept_3_2 52 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 278 (accept_3_2 49 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 278 (Polychromatic418967fa.accept_17_14_7_6_1_11222 48 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 278 (accept_3_2 46 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 278
  (Polychromatic418967fa.accept_19_6_18_12_1_6125 44 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 278 (accept_3_2 43 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 278 (accept_3_2 40 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 278 (accept_3_2 37 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 278 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 278 (accept_3_2 34 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 278 (accept_3_2 31 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 278 (accept_3_2 28 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 278 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 278
  (Polychromatic418967fa.accept_19_7_18_12_1_3427 26 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 278 (accept_3_2 25 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 278 (accept_3_2 22 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 278 (accept_3_2 19 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 278 (accept_3_2 16 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 278 (accept_3_2 13 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 278 (accept_3_2 10 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 278
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 278 (accept_3_2 7 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 278 (accept_3_2 4 75 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  75 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 278 (accept_3_2 1 75 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 278 (allA_succ_of_accept
  73 74 278 (accept_3_2 73 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 278 2 36 37 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 278 2 35 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 278 2 34 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 278 (accept_3_2 67 74 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 278 2 33 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 278 2 32 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 278
  (Polychromatic418967fa.accept_19_6_17_12_1_10550 63 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 74 278 2 31 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 74 278 (accept_3_2 61 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 278 2 30 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 278 2 29 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 278 2 28 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 278 (accept_3_2 55 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 278 2 27 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 278 (Polychromatic418967fa.accept_13_1_9_5_1_1598 53 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 278 2 26 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 278 2 25 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 278 (accept_3_2 49 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 278 2 24 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 278 (Polychromatic418967fa.accept_25_22_24_3_1_17042 47 74 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 278 2 23 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 278
  (Polychromatic418967fa.accept_22_1_8_14_1_14026 45 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 278 2 22 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 278 (accept_3_2 43 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 278 2 21 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 278 2 20 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 278 2 19 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 278 (accept_3_2 37 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 278 2 18 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 278 2 17 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 278 2 16 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 278 (accept_3_2 31 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 278 2 15 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 278 2 14 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 278 2 13 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 278 (accept_3_2 25 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 278 2 12 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 74 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 278 2 11 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 278 2 10 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 278 (accept_3_2 19 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 278 2 9 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 74 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 278 2 8 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 278 2 7 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 278 (accept_3_2 13
  74 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 278 2 6 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 278
  (Polychromatic418967fa.accept_22_11_8_14_1_12552 11 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 278 2 5 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 74 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 278 2 4 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 278 (accept_3_2 7 74 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 278 2 3 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 278 2 2 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 278 2 1 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 278 (accept_3_2 1 74 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 278 (allA_of_3_0 73 73 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 278 (allA_succ_of_accept 71 72 278
  (Polychromatic418967fa.accept_15_11_12_8_1_739 71 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 278 2 35 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 278 (Polychromatic418967fa.accept_22_3_6_14_1_17041 69 72 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 278 2 34 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 278 (accept_3_2 67 72 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 278 2 33 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 65 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 278 2 32 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 72 278 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 278 2 31 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 278 (accept_3_2 61 72 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 278 2 30 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59
  72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 278 2 29 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 278
  (Polychromatic418967fa.accept_21_15_9_5_1_6588 57 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 278 2 28 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 278 (accept_3_2 55 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 278 2 27 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 278 2 26 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 278
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 51 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 278 2 25 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 72 278 (accept_3_2 49 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 278 2 24 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 278 (Polychromatic418967fa.accept_22_3_6_14_1_17041 47 72 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 278 2 23 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 278 2 22 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 72 278 (accept_3_2 43 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 278 2 21 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 278 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 278 2 20 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 72 278 2 19 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 72 278 (accept_3_2 37 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 278 2 18 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 278 2 17 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 278
  (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 278 2 16 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 278 (accept_3_2 31 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 278 2 15 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 278 (Polychromatic418967fa.accept_23_6_3_2_1_17040 29 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 278 2 14 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 278
  (Polychromatic418967fa.accept_17_10_4_6_1_3757 27 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 278 2 13 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 72 278 (accept_3_2 25 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 278 2 12 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 278 (Polychromatic418967fa.accept_25_23_22_3_1_8234 23 72 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 278 2 11 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 278
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 278 2 10 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 278 (accept_3_2 19 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 278 2 9 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 278 2 8 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 15
  72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 278 2 7 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 278 (accept_3_2 13
  72 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 278 2 6 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 278 2 5 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 278 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 278 2 4 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 278 (accept_3_2 7 72 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 72 278 2 3 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 72 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 278 2 2 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 278 2 1 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 278 (accept_3_2 1 72
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 278 (allA_succ_of_accept 70
  71 278 (accept_3_2 70 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 71 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 278 (accept_3_2 67 71 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 278 (accept_3_2 64 71
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 278 (accept_3_2 61 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 278 (accept_3_2 58 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 278 (accept_3_2 55 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 278 (Polychromatic418967fa.accept_19_16_14_12_1_6261 54 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 278 (accept_3_2 52 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 278
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 50 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 278 (accept_3_2 49 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 278 (Polychromatic418967fa.accept_16_15_7_6_1_1453 47 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 278 (accept_3_2 46 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 278 (accept_3_2 43 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 278 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 278 (accept_3_2 40 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 278 (accept_3_2 37 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 278 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 278 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 278 (accept_3_2 34 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 278 (accept_3_2 31 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 278 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 278 (accept_3_2 28 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 278
  (Polychromatic418967fa.accept_17_9_3_6_1_11232 26 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 278 (accept_3_2 25 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 278 (accept_3_2 22 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 278 (accept_3_2 19 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 278 (accept_3_2 16 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 278
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 278 (accept_3_2 13 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 278 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 278 (accept_3_2 10 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 278 (accept_3_2 7 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 278 (accept_3_2 4 71 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 278 (Polychromatic418967fa.accept_18_2_17_8_1_1893
  2 71 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 278 (accept_3_2 1 71
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 278 (allA_of_3_0 70 70 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 278 (allA_succ_of_accept 68 69 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 278 (accept_3_2 67 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 278 (accept_3_2 64 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 278
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 62 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 278 (accept_3_2 61 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 278 (accept_3_2 58 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 278 (accept_3_2 55 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 278 (accept_3_2 52 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 278 (accept_3_2 49 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 278 (accept_3_2 46 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 278 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 278 (accept_3_2 43 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 278 (accept_3_2 40 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 278 (accept_3_2 37 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 278 (accept_3_2 34 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 278 (accept_3_2 31 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 278 (accept_3_2 28 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 278
  (Polychromatic418967fa.accept_22_4_3_14_1_15620 26 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 278 (accept_3_2 25 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 278 (accept_3_2 22 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 278 (accept_3_2 19 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 278 (accept_3_2 16 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 278 (accept_3_2 13 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 278 (accept_3_2 10 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 69 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 278 (accept_3_2 7 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  278 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 278 (accept_3_2 4 69 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  69 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 278 (accept_3_2 1 69 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 278 (allA_succ_of_accept 67 68
  278 (accept_3_2 67 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 278 2 33 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 278 2 32 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 68 278 (Polychromatic418967fa.accept_13_11_3_5_1_982 63 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 278 2 31 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 278 (accept_3_2 61 68 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 278 2 30 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  59 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 278 2 29 34 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 278 2 28 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 68 278 (accept_3_2 55 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 68 278 2 27 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 68 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 278 2 26 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 278 2 25 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 68 278 (accept_3_2 49 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 278 2 24 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 68 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 278 2 23 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 278 2 22 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 68 278 (accept_3_2 43 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 68 278 2 21 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 68 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 278 2 20 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 278 2 19 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 278 (accept_3_2 37 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 278 2 18 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 68 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 278 2 17 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 278 2 16 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 68 278 (accept_3_2 31 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 68 278 2 15 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 68 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 278 2 14 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 278
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 278 2 13 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 68 278 (accept_3_2 25 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 68 278 2 12 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 68 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 278 2 11 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 278 2 10 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 68 278 (accept_3_2 19 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 68 278 2 9 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 68 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 68 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 278 2 8 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 278 2 7 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 278 (accept_3_2 13
  68 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 278 2 6 34 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 278 2 5 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 278 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 68 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 278 2 4 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 278 (accept_3_2 7 68 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 278 2 3 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 278 2 2 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 278 2 1 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 278 (accept_3_2 1 68
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 278 (allA_of_3_0 67 67 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 278 (allA_succ_of_accept 65 66 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 278 2 32 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 278 2 31 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 278 (accept_3_2 61 66 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 278 2 30 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 59
  66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 278 2 29 33 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 278 2 28 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 278 (accept_3_2 55 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 278 2 27 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 278 2 26 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 278 2 25 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 278 (accept_3_2 49 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 278 2 24 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 278 2 23 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 278 2 22 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 278 (accept_3_2 43 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 278 2 21 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 278 2 20 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 278 2 19 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 278 (accept_3_2 37 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 278 2 18 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 278 (Polychromatic418967fa.accept_13_9_1_5_1_964 35 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 278 2 17 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 278 2 16 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 278 (accept_3_2 31 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 278 2 15 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 278 2 14 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 278 2 13 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 278 (accept_3_2 25 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 278 2 12 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 278 2 11 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 278 2 10 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 278 (accept_3_2 19 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 278 2 9 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 278 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 66 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 278 2 8 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 278 2 7 33 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 278 (accept_3_2 13
  66 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 278 2 6 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 278 2 5 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 278 2 4 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 278 (accept_3_2 7 66 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 278 2 3 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 278 2 2 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  66 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 278 2 1 33 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 278 (accept_3_2 1 66
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 278 (allA_succ_of_accept 64 65 278
  (accept_3_2 64 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 65 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 278 (accept_3_2 61 65 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 278 (accept_3_2 58 65
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 278 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 278 (accept_3_2 55 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 278 (Polychromatic418967fa.accept_17_3_14_6_1_3742 54 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 278 (accept_3_2 52 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 278 (accept_3_2 49 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 278 (accept_3_2 46 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 278 (accept_3_2 43 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 278 (accept_3_2 40 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 278 (accept_3_2 37 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 278 (Polychromatic418967fa.accept_20_16_5_18_1_2846 36 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 278 (accept_3_2 34 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 278 (accept_3_2 31 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 278 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 278 (accept_3_2 28 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 278
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 278 (accept_3_2 25 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 278 (accept_3_2 22 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 278 (accept_3_2 19 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 278 (accept_3_2 16 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 278 (accept_3_2 13 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 278 (accept_3_2 10 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 278 (accept_3_2 7 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 278 (accept_3_2 4 65 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  65 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 278 (accept_3_2 1 65 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 278 (allA_of_3_0 64 64 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 278 (allA_succ_of_accept 62 63 278
  (Polychromatic418967fa.accept_17_11_12_6_1_6070 62 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 278 (accept_3_2 61 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 278 (accept_3_2 58 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 278 (accept_3_2 55 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 278 (accept_3_2 52 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 278 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 278
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 278 (accept_3_2 49 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 278 (Polychromatic418967fa.accept_19_10_6_12_1_10562 48 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 278 (accept_3_2 46 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 278
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 278 (accept_3_2 43 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 278 (accept_3_2 40 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 278
  (Polychromatic418967fa.accept_11_5_8_3_1_66 38 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 278 (accept_3_2 37 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 278 (accept_3_2 34 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 278
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 278 (accept_3_2 31 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 278 (accept_3_2 28 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 278 (accept_3_2 25 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 278 (accept_3_2 22 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 278
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 278 (accept_3_2 19 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 278 (accept_3_2 16 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 278 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 278
  (Polychromatic418967fa.accept_19_14_6_12_1_13167 14 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 63 278 (accept_3_2 13 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 278 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 63 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 278 (accept_3_2 10 63 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 278
  (Polychromatic418967fa.accept_19_8_6_12_1_13105 8 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 278 (accept_3_2 7 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 278 (accept_3_2 4 63 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 278 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 63 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 278
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 278 (accept_3_2 1 63 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 278 (allA_succ_of_accept 61 62 278
  (accept_3_2 61 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 278 2 30 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 278
  (Polychromatic418967fa.accept_11_4_7_3_1_289 59 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 278 2 29 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 278 2 28 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 278 (accept_3_2 55 62 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 278 2 27 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 278 2 26 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 278
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 51 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 278 2 25 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 278 (accept_3_2 49 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 278 2 24 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 278 (Polychromatic418967fa.accept_13_8_10_5_1_977 47 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 278 2 23 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 278 2 22 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 278 (accept_3_2 43 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 278 2 21 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 278 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 278 2 20 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 278 2 19 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 278 (accept_3_2 37 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 278 2 18 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 278 2 17 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 278
  (Polychromatic418967fa.accept_20_13_2_18_1_1682 33 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 278 2 16 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 278 (accept_3_2 31 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 278 2 15 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 278 2 14 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 278
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 278 2 13 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 278 (accept_3_2 25 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 278 2 12 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 278 (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 278 2 11 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 278
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 278 2 10 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 278 (accept_3_2 19 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 278 2 9 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 278 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 62 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 278 2 8 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 278 2 7 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 278 (accept_3_2 13
  62 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 278 2 6 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 278 2 5 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 278 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 62 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 278 2 4 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 278 (accept_3_2 7 62 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 278 2 3 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 278 2 2 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 278 (Polychromatic418967fa.accept_20_3_2_18_1_11577
  3 62 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 278 2 1 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 278 (accept_3_2 1 62
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 278 (allA_of_3_0 61 61 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 278 (allA_succ_of_accept 59 60 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 278 2 29 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 278 2 28 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 278 (accept_3_2 55 60 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 278 2 27 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 278 (Polychromatic418967fa.accept_13_1_8_5_1_2315
  53 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 278 2 26 30 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 278 2 25 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 278 (accept_3_2 49 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 278 2 24 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 60 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 278 2 23 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 278
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 60 278 2 22 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 60 278 (accept_3_2 43 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 278 2 21 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 278 2 20 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 278 2 19 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 278 (accept_3_2 37 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 278 2 18 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 60 278 (Polychromatic418967fa.accept_21_14_18_5_1_8196 35 60 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 278 2 17 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 278
  (Polychromatic418967fa.accept_17_16_9_6_1_3723 33 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 278 2 16 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 60 278 (accept_3_2 31 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 278 2 15 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 278 2 14 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 278 2 13 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 60 278 (accept_3_2 25 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 278 2 12 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 278 2 11 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 278 2 10 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 60 278 (accept_3_2 19 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 278 2 9 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 278 (Polychromatic418967fa.accept_19_17_3_12_1_13140 17 60 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 278 2 8 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 278 2 7 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 278 (accept_3_2 13
  60 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 278 2 6 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 278 2 5 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 278 2 4 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 278 (accept_3_2 7 60 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 60 278 2 3 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 60 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 278 2 2 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 278 2 1 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 278 (accept_3_2 1 60
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 278 (allA_succ_of_accept 58 59 278
  (accept_3_2 58 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 278 (accept_3_2 55 59 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 278 (accept_3_2 52 59
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 278 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 278 (accept_3_2 49 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 278 (accept_3_2 46 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 278 (accept_3_2 43 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 278 (accept_3_2 40 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 278 (accept_3_2 37 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 278 (accept_3_2 34 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 278 (accept_3_2 31 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 278 (accept_3_2 28 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 278
  (Polychromatic418967fa.accept_17_9_8_6_1_6050 26 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 278 (accept_3_2 25 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 278 (accept_3_2 22 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 278 (accept_3_2 19 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 278 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 278 (accept_3_2 16 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 278 (accept_3_2 13 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 278 (accept_3_2 10 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 278 (accept_3_2 7 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 278 (accept_3_2 4 59 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 278 (accept_3_2 1 59 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 278 (allA_of_3_0 58 58 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 278
  (allA_succ_of_accept 56 57 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 278 (accept_3_2 55 57 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 278 (accept_3_2 52 57
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62
  51 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 278 (accept_3_2 49 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 278 (accept_3_2 46 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 278
  (Polychromatic418967fa.accept_23_21_11_2_1_17039 44 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 57 278 (accept_3_2 43 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 278 (accept_3_2 40 57 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 278 (accept_3_2 37 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 278 (Polychromatic418967fa.accept_23_13_11_2_1_3894 36 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 278 (accept_3_2 34 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 278 (accept_3_2 31 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 278 (accept_3_2 28 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 278
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 278 (accept_3_2 25 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 278 (accept_3_2 22 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 278 (Polychromatic418967fa.accept_20_1_17_18_1_1678 21 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 278 (accept_3_2 19 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 278 (accept_3_2 16 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 278 (accept_3_2 13 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 278 (accept_3_2 10 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 57 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 278
  (Polychromatic418967fa.accept_21_8_15_5_1_8178 8 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 278 (accept_3_2 7 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 278 (accept_3_2 4 57 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  57 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 278 (accept_3_2 1 57 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 278 (allA_succ_of_accept 55 56 278 (accept_3_2 55 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 278 2 27 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 278 2 26 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 278 2 25 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 278 (accept_3_2 49 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 278 2 24 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 56 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 278 2 23 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 278
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 278 2 22 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 56 278 (accept_3_2 43 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 56 278 2 21 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 56 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 278 2 20 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 278 2 19 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 278 (accept_3_2 37 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 278 2 18 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 56 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 278 2 17 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 278 2 16 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 278 (accept_3_2 31 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 278 2 15 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 56 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 278 2 14 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 278
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 278 2 13 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 56 278 (accept_3_2 25 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 56 278 2 12 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 278 2 11 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 278 2 10 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 56 278 (accept_3_2 19 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 56 278 2 9 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 56 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 278 2 8 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 278 2 7 28 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 278 (accept_3_2 13
  56 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 278 2 6 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 278
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 278 2 5 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 56 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 278 2 4 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 278 (accept_3_2 7 56 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 278 2 3 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 278 2 2 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 278 2 1 28 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 278 (accept_3_2 1 56
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 278))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 278 (allA_of_3_0 55 55 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 278
  (allA_succ_of_accept 53 54 278 (Polychromatic418967fa.accept_19_15_16_12_1_4779 53 54 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 278 2 26 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 278 (Polychromatic418967fa.accept_11_7_10_3_1_633
  51 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 278 2 25 27 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 278
  (accept_3_2 49 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 278 2 24 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 278
  (Polychromatic418967fa.accept_15_2_9_8_1_736 47 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 278 2 23 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 54 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 278 2 22 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 278 (accept_3_2 43 54 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 278 2 21 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 278
  (Polychromatic418967fa.accept_24_17_6_14_1_11994 41 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 278 2 20 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 54 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 278 2 19 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 278 (accept_3_2 37 54 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 278 2 18 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 278
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 278 2 17 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 278 2 16 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 278 (accept_3_2 31 54 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 278 2 15 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 29
  54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 278 2 14 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 278 2 13 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 278 (accept_3_2 25 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 278 2 12 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 278 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 54 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 278 2 11 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 278 2 10 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 278 (accept_3_2 19 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 278 2 9 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 278 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 54 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 278 2 8 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 278 2 7 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 278 (accept_3_2 13
  54 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 278 2 6 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 278
  (Polychromatic418967fa.accept_21_11_12_5_1_2224 11 54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 278 2 5 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 278 2 4 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 278 (accept_3_2 7 54 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 278 2 3 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 278 (Polychromatic418967fa.accept_17_5_3_6_1_12347 5 54 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 278 2 2 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  54 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 278 2 1 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 278 (accept_3_2 1 54
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 278))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 278 (allA_succ_of_accept 52 53 278 (accept_3_2 52 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 278 (accept_3_2 49 53 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 48
  53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 278 (accept_3_2 46 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 278 (accept_3_2 43 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 278 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 278 (accept_3_2 40 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 278 (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 278 (accept_3_2 37 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 278 (accept_3_2 34 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 278 (accept_3_2 31 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 278 (accept_3_2 28 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 278 (accept_3_2 25 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 278 (Polychromatic418967fa.accept_19_5_15_12_1_6273 24 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 278 (accept_3_2 22 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 278 (accept_3_2 19 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 278 (Polychromatic418967fa.accept_17_1_2_6_1_818 18 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 278
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 278 (accept_3_2 16 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 278 (Polychromatic418967fa.accept_21_14_11_5_1_6591 14 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 278 (accept_3_2 13 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 278 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 53
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 278 (accept_3_2 10 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 278 (accept_3_2 7 53 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 278
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 278 (accept_3_2 4 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 278 (accept_3_2 1 53 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 278))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 278 (allA_of_3_0 52 52
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 278 (allA_succ_of_accept 50 51 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 278 (accept_3_2 49 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 278 (accept_3_2 46 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 278
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 278 (accept_3_2 43 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 278 (accept_3_2 40 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 278 (accept_3_2 37 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 278 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 278 (accept_3_2 34 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 278 (accept_3_2 31 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 278 (accept_3_2 28 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 278
  (Polychromatic418967fa.accept_11_4_7_3_1_289 26 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 278 (accept_3_2 25 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 278 (accept_3_2 22 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 278 (accept_3_2 19 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 278 (accept_3_2 16 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 278 (accept_3_2 13 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 278 (accept_3_2 10 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 278
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 278 (accept_3_2 7 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  278 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 278 (accept_3_2 4 51 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  51 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 278 (accept_3_2 1 51 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 278)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 278 (allA_succ_of_accept 49 50 278 (accept_3_2 49 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 278 2 24 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 278 2 23 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 50 278 2 22 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 50 278 (accept_3_2 43 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 278 2 21 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 278 2 20 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 278 2 19 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 278 (accept_3_2 37 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 278 2 18 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 278 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 278 2 17 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 278 2 16 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 278 (accept_3_2 31 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 278 2 15 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 278 2 14 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 278 2 13 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 278 (accept_3_2 25 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 278 2 12 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 278 2 11 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 278 2 10 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 278 (accept_3_2 19 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 278 2 9 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 278 2 8 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 278 2 7 25 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 278 (accept_3_2 13
  50 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 278 2 6 25 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 278 2 5 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 278 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 50 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 278 2 4 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 278 (accept_3_2 7 50 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 278 2 3 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 50 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 278 2 2 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 278 2 1 25 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 278 (accept_3_2 1 50
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 278))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 278 (allA_of_3_0 49 49 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 278
  (allA_succ_of_accept 47 48 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 278 2 23 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 278 (Polychromatic418967fa.accept_21_3_6_5_1_8187
  45 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 278 2 22 24 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 278
  (accept_3_2 43 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 278 2 21 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 278 2 20 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 278 2 19 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 278 (accept_3_2 37 48 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 278 2 18 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 278 (Polychromatic418967fa.accept_15_5_3_8_1_748 35
  48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 278 2 17 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 278 2 16 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 278 (accept_3_2 31 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 278 2 15 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 278 2 14 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 278
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 278 2 13 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 48 278 (accept_3_2 25 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 278 2 12 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 278 2 11 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 278
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 278 2 10 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 278 (accept_3_2 19 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 278 2 9 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 278 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 48 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 278 2 8 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 278 2 7 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 278 (accept_3_2 13
  48 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 278 2 6 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 278 2 5 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 48 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 48 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 278 2 4 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 278 (accept_3_2 7 48 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 48 278 2 3 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 48 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 278 2 2 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 278 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3
  48 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 278 2 1 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 278 (accept_3_2 1 48
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 278))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 47 278 (allA_succ_of_accept 46 47 278 (accept_3_2 46 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 278 (accept_3_2 43 47 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42
  47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 278 (accept_3_2 40 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 278 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 278 (accept_3_2 37 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 278 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 278
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 278 (accept_3_2 34 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 278 (accept_3_2 31 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 278 (accept_3_2 28 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 278 (Polychromatic418967fa.accept_22_4_3_14_1_15620 26 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 278 (accept_3_2 25 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 278 (accept_3_2 22 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 278 (accept_3_2 19 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 278 (Polychromatic418967fa.accept_19_18_9_12_1_6153 18 47
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 278 (accept_3_2 16 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 278 (accept_3_2 13 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 278
  (Polychromatic418967fa.accept_17_11_13_6_1_2625 11 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 278 (accept_3_2 10 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 47 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 278 (accept_3_2 7 47 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 278 (accept_3_2 4 47 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 278
  (Polychromatic418967fa.accept_17_2_13_6_1_3772 2 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 278 (accept_3_2 1 47 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  278))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 278 (allA_of_3_0 46 46 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 278 (allA_succ_of_accept 44 45 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 278 (accept_3_2 43 45 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 278 (Polychromatic418967fa.accept_10_2_5_8_1_139
  42 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 278 (accept_3_2 40 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 278 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 278 (accept_3_2 37 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 278 (accept_3_2 34 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  45 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 278 (accept_3_2 31 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 278 (accept_3_2 28 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  45 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 45 278 (Polychromatic418967fa.accept_23_3_22_2_1_12322 26 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 278 (accept_3_2 25 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 278 (accept_3_2 22 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 278 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 45 278 (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 278 (accept_3_2 19 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 278 (accept_3_2 16 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  45 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 45 278 (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 278 (accept_3_2 13 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 278 (accept_3_2 10 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  45 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 45 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 278 (accept_3_2 7 45 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 45 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 278 (accept_3_2 4 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 278 (accept_3_2 1 45 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 45 278))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 278 (allA_succ_of_accept 43 44
  278 (accept_3_2 43 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 278 2 21 22 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 278
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 278 2 20 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 44 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 278 2 19 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 278 (accept_3_2 37 44 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 278 2 18 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  35 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 278 2 17 22 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 278
  (Polychromatic418967fa.accept_17_16_10_6_1_7313 33 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 278 2 16 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 44 278 (accept_3_2 31 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 44 278 2 15 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 44 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 278 2 14 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 278
  (Polychromatic418967fa.accept_19_8_6_12_1_13105 27 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 278 2 13 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 278 (accept_3_2 25 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 278 2 12 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 278 2 11 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 278
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 278 2 10 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 44 278 (accept_3_2 19 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 44 278 2 9 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 44 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 278 2 8 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 278 (Polychromatic418967fa.accept_19_15_6_12_1_7746
  15 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 278 2 7 22 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 278 (accept_3_2 13
  44 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 278 2 6 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 278 2 5 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 278 2 4 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 278 (accept_3_2 7 44 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 278 2 3 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 44 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 278 2 2 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 278 2 1 22 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 278 (accept_3_2 1 44
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 278)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 278 (allA_of_3_0 43 43 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 278 (allA_succ_of_accept 41 42
  278 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 278 2 20 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 278 2 19 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 278 (accept_3_2 37 42 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 278 2 18 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35
  42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 278 2 17 21 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 278 2 16 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 278 (accept_3_2 31 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 278 2 15 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 278 2 14 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 278 2 13 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 278 (accept_3_2 25 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 278 2 12 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 278 2 11 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 278 2 10 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 278 (accept_3_2 19 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 278 2 9 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 42 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 278 2 8 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 15
  42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 278 2 7 21 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 278 (accept_3_2 13
  42 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 278 2 6 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 278 2 5 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 278 2 4 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 278 (accept_3_2 7 42 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 278 2 3 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 278 2 2 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 278 2 1 21 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 278 (accept_3_2 1 42
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 278)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  278 (allA_succ_of_accept 40 41 278 (accept_3_2 40 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 278 (accept_3_2 37 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 278 (accept_3_2 34 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 278 (accept_3_2 31 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 278 (accept_3_2 28 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 278 (Polychromatic418967fa.accept_19_7_3_12_1_4787 26 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 278 (accept_3_2 25 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 278 (accept_3_2 22 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 278 (accept_3_2 19 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 278
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 278 (accept_3_2 16 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 278 (Polychromatic418967fa.accept_17_14_7_6_1_11222 14 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 278 (accept_3_2 13 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 278 (accept_3_2 10 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 278 (accept_3_2 7 41 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 278
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 278 (accept_3_2 4 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 278 (accept_3_2 1 41 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 278))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 278 (allA_of_3_0 40 40 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 278 (allA_succ_of_accept 38 39 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 278 (accept_3_2 37 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 278 (accept_3_2 34 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 278 (accept_3_2 31 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 278 (accept_3_2 28 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 278
  (Polychromatic418967fa.accept_19_7_1_12_1_6134 26 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 278 (accept_3_2 25 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 278 (accept_3_2 22 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 278 (accept_3_2 19 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 278 (accept_3_2 16 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 278 (accept_3_2 13 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 278 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 278 (accept_3_2 10 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 278 (accept_3_2 7 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 278 (accept_3_2 4 39 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  39 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 278 (accept_3_2 1 39 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 278))))))))))))))))))))))))))))))))))))))) (allB_succ 38 278
  (allA_succ_of_accept 37 38 278 (accept_3_2 37 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  278 2 18 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 278 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 278 2 17 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 278 2 16 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 278 (accept_3_2 31 38 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 278 2 15 19 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 278 2 14 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 38 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 278 2 13 19 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 278 (accept_3_2 25 38 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 278 2 12 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 278 2 11 19 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 278 2 10 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 278 (accept_3_2 19 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 278 2 9 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 278 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 38 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 278 2 8 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 278 2 7 19 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 278 (accept_3_2 13
  38 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 278 2 6 19 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 278
  (Polychromatic418967fa.accept_17_11_4_6_1_2631 11 38 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 278 2 5 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 278 2 4 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 278 (accept_3_2 7 38 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 278 2 3 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 278 2 2 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 278 2 1 19 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 278 (accept_3_2 1 38
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 278)))))))))))))))))))))))))))))))))))))) (allB_succ 37 278
  (allA_of_3_0 37 37 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 278 (allA_succ_of_accept 35 36 278
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 35 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 278 2 17 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 36 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 278 2 16 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 278 (accept_3_2 31 36 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 278 2 15 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 278 (Polychromatic418967fa.accept_15_14_6_8_1_1410
  29 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 278 2 14 18 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 278 2 13 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 278 (accept_3_2 25 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 278 2 12 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 36 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 278 2 11 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 278
  (Polychromatic418967fa.accept_13_8_10_5_1_977 21 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 278 2 10 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 278 (accept_3_2 19 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 278 2 9 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 278 2 8 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 278 (Polychromatic418967fa.accept_13_2_10_5_1_1643
  15 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 278 2 7 18 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 278 (accept_3_2 13
  36 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 278 2 6 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 278 2 5 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 278 (Polychromatic418967fa.accept_21_9_15_5_1_3500 9 36 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 278 2 4 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 278 (accept_3_2 7 36 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 36 278 2 3 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 36 278 (Polychromatic418967fa.accept_16_5_4_6_1_3349 5 36 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 278 2 2 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 278 2 1 18 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 278 (accept_3_2 1 36
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 278)))))))))))))))))))))))))))))))))))) (allB_succ 35 278
  (allA_succ_of_accept 34 35 278 (accept_3_2 34 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 278 (accept_3_2 31 35 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 278 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 278 (accept_3_2 28 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 278 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 278 (accept_3_2 25 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 278 (Polychromatic418967fa.accept_19_5_16_12_1_6175 24 35
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 278
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 278 (accept_3_2 22 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 278 (accept_3_2 19 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 35 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 278 (accept_3_2 16 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 278 (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 35 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 278 (accept_3_2 13 35 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 35 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 278
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 278 (accept_3_2 10 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 278 (accept_3_2 7 35 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 278 (Polychromatic418967fa.accept_19_6_16_12_1_6118 6 35 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 278 (accept_3_2 4 35 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 278 (accept_3_2 1 35 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  278))))))))))))))))))))))))))))))))))) (allB_succ 34 278 (allA_of_3_0 34 34 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 278 (allA_succ_of_accept 32 33 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 33 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 278 (accept_3_2 31 33 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 278 (accept_3_2 28 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 278 (accept_3_2 25 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 278 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 33 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 278 (accept_3_2 22 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 278 (accept_3_2 19 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 33 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 278 (accept_3_2 16 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 278 (accept_3_2 13 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 278 (accept_3_2 10 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 278 (Polychromatic418967fa.accept_20_8_13_18_1_7110 8 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 278 (accept_3_2 7 33 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 278 (accept_3_2 4 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 278 (accept_3_2 1 33 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 278))))))))))))))))))))))))))))))))) (allB_succ 32 278 (allA_succ_of_accept 31 32 278
  (accept_3_2 31 32 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 278 2 15 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 278 2 14 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 278 2 13 16 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 278 (accept_3_2 25 32 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 278 2 12 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  32 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 278 2 11 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 278 2 10 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 32 278 (accept_3_2 19 32 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 32 278 2 9 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 32 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 32 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 278 2 8 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  32 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 278 2 7 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 278 (accept_3_2 13
  32 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 278 2 6 16 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 32 278 2 5 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 32 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 278 2 4 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 278 (accept_3_2 7 32 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 32 278 2 3 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 32 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 32 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 278 2 2 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 278 2 1 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 278 (accept_3_2 1 32
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 278)))))))))))))))))))))))))))))))) (allB_succ 31 278
  (allA_of_3_0 31 31 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 278 (allA_succ_of_accept 29 30 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 278 2 14 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 30 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 278 2 13 15 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 278 (accept_3_2 25 30 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 278 2 12 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  30 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 278 2 11 15 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 278 2 10 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 278 (accept_3_2 19 30 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 278 2 9 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 278 2 8 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  30 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 278 2 7 15 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 278 (accept_3_2 13
  30 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 278 2 6 15 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 278 2 5 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 278 2 4 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 278 (accept_3_2 7 30 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 278 2 3 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 278 2 2 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 278 2 1 15 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 278 (accept_3_2 1 30
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 278)))))))))))))))))))))))))))))) (allB_succ 29 278
  (allA_succ_of_accept 28 29 278 (accept_3_2 28 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 278 (accept_3_2 25 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 278 (accept_3_2 22 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 278 (accept_3_2 19 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 278 (accept_3_2 16 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 278 (accept_3_2 13 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 278 (accept_3_2 10 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 278 (accept_3_2 7 29 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 278 (accept_3_2 4 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 29 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 278 (accept_3_2 1 29 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 278))))))))))))))))))))))))))))) (allB_succ 28 278 (allA_of_3_0 28 28 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 278 (allA_succ_of_accept 26 27 278 (Polychromatic418967fa.accept_15_11_12_8_1_739
  26 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 278 (accept_3_2 25
  27 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 278
  (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 278 (accept_3_2 22 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 278 (Polychromatic418967fa.accept_14_6_13_12_1_810
  20 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 278 (accept_3_2 19
  27 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 278 (accept_3_2 16 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 278 (Polychromatic418967fa.accept_23_14_4_2_1_1181
  14 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 278 (accept_3_2 13
  27 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 278
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 278 (accept_3_2 10 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 278 (accept_3_2 7 27 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 6
  27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 278 (accept_3_2 4 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  278 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 27 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 278 (Polychromatic418967fa.accept_16_2_11_6_1_737 2 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 278 (accept_3_2 1 27 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 278))))))))))))))))))))))))))) (allB_succ 26 278 (allA_succ_of_accept 25 26 278 (accept_3_2
  25 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 278 2 12 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 278 2 11 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 278 (Polychromatic418967fa.accept_22_21_4_14_1_11011 21 26 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 278 2 10 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 278 (accept_3_2 19 26 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 278 2 9 13 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 278
  (Polychromatic418967fa.accept_25_17_1_3_1_13590 17 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 278 2 8 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 278 (Polychromatic418967fa.accept_17_15_9_6_1_8705 15 26 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 278 2 7 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 278 (accept_3_2 13 26 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 278 2 6 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 278 (Polychromatic418967fa.accept_19_11_7_12_1_4770 11 26
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 278 2 5 13 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 278
  (Polychromatic418967fa.accept_25_9_1_3_1_13624 9 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 278 2 4 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 278 (accept_3_2 7 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 278
  2 3 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  278 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 26 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 26 278 2 2 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 26 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 26 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 278 2 1 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 278 (accept_3_2 1 26 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 26 278)))))))))))))))))))))))))) (allB_succ 25 278 (allA_of_3_0 25 25 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 24 278 (allA_succ_of_accept 23 24 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 278 2 11 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 24 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 278 2 10 12 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 278 (accept_3_2 19 24 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 278 2 9 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 278 (Polychromatic418967fa.accept_15_2_9_8_1_736 17
  24 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 278 2 8 12 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 278 2 7 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 278 (accept_3_2 13 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24
  278 2 6 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  24 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 278 2 5 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 24 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 278 2 4 12 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 278 (accept_3_2 7 24 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 278 2 3 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 278 2 2 12 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 278 2 1 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 278 (accept_3_2 1 24 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  278)))))))))))))))))))))))) (allB_succ 23 278 (allA_succ_of_accept 22 23 278 (accept_3_2 22 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 278 (accept_3_2 19 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 278 (accept_3_2 16 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 278
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 278 (accept_3_2 13 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 278 (accept_3_2 10 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 278 (accept_3_2 7 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 278 (accept_3_2 4 23 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 278 (accept_3_2 1 23 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 278))))))))))))))))))))))) (allB_succ 22 278 (allA_of_3_0 22 22
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 278 (allA_succ_of_accept 20 21 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 278 (accept_3_2 19 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 278 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 278 (accept_3_2 16 21 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 278 (accept_3_2 13 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 278 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 278 (accept_3_2 10 21 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 278 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 278
  (Polychromatic418967fa.accept_20_8_1_18_1_7103 8 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 278 (accept_3_2 7 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 278 (accept_3_2 4 21 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 278 (accept_3_2 1 21 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 278))))))))))))))))))))) (allB_succ 20 278 (allA_succ_of_accept
  19 20 278 (accept_3_2 19 20 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 278 2 9 10 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 278
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 20 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 278 2 8 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 278 2 7 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 278 (accept_3_2 13 20 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 278 2 6 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 278 2 5 10 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 278
  (Polychromatic418967fa.accept_17_9_3_6_1_11232 9 20 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 278 2 4 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 278 (accept_3_2 7 20 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 278
  2 3 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 278 2 2 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 278 2 1 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 278 (accept_3_2 1 20 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 278)))))))))))))))))))) (allB_succ 19 278 (allA_of_3_0 19 19 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 278 (allA_succ_of_accept 17 18 278 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 18 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 278 2 8 9 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 278 2 7 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 278 (accept_3_2 13 18 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  278 2 6 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 278 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 18 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 278 2 5 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 278 2 4 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 278 (accept_3_2 7 18 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 278 2 3 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 278 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 18 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 278 2 2 9 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 18 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 278 2 1 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 278 (accept_3_2 1 18 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  278)))))))))))))))))) (allB_succ 17 278 (allA_succ_of_accept 16 17 278 (accept_3_2 16 17 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 278
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 278 (accept_3_2 13 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 278 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 278 (accept_3_2 10 17 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 278 (accept_3_2 7 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  278 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 17 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 278 (accept_3_2 4 17 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 278 (accept_3_2 1 17 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  278))))))))))))))))) (allB_succ 16 278 (allA_of_3_0 16 16 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  278 (allA_succ_of_accept 14 15 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 278 (accept_3_2 13 15 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 278 (accept_3_2 10 15
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  15 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 278
  (Polychromatic418967fa.accept_17_8_15_6_1_4889 8 15 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 278 (accept_3_2 7 15 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 278 (accept_3_2 4 15 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  15 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 278 (accept_3_2 1 15 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 278))))))))))))))) (allB_succ 14 278 (allA_succ_of_accept 13 14
  278 (accept_3_2 13 14 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 278 2 6 7 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 278 2 5 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 278 2 4 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 278 (accept_3_2 7 14 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 278 2 3 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 14 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 278 2 2 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 278 2 1 7 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 278 (accept_3_2 1 14
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 278)))))))))))))) (allB_succ 13 278 (allA_of_3_0 13 13 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 278 (allA_succ_of_accept 11 12 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 278 2 5 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 278 (Polychromatic418967fa.accept_21_9_12_5_1_317 9 12 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 278 2 4 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 278 (accept_3_2 7 12 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 278 2 3 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 278 2 2 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 3
  12 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 278 2 1 6 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 278 (accept_3_2 1 12
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 278)))))))))))) (allB_succ 11 278 (allA_succ_of_accept 10 11
  278 (accept_3_2 10 11 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 278 (accept_3_2 7 11 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 278 (accept_3_2 4 11 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 11 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 278 (accept_3_2 1 11 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  278))))))))))) (allB_succ 10 278 (allA_of_3_0 10 10 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 278
  (allA_succ_of_accept 8 9 278 (Polychromatic418967fa.accept_17_8_9_6_1_7330 8 9 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 278 (accept_3_2 7 9 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 9 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 278 (accept_3_2 4 9 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 278
  (Polychromatic418967fa.accept_13_2_9_5_1_959 2 9 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 278 (accept_3_2 1 9 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 278)))))))))
  (allB_succ 8 278 (allA_succ_of_accept 7 8 278 (accept_3_2 7 8 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 278 2 3 4 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 8 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 278 2 2 4 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 278 2 1 4 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 278 (accept_3_2 1 8 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 278)))))))) (allB_succ 7 278 (allA_of_3_0 7 7 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 278 (allA_succ_of_accept 5 6 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 278 2 2 3 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 278 2 1 3 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 278 (accept_3_2 1 6 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 278))))))
  (allB_succ 5 278 (allA_succ_of_accept 4 5 278 (accept_3_2 4 5 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 278 (accept_3_2 1 5 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 278))))) (allB_succ 4 278 (allA_of_3_0 4 4 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 278 (allA_succ_of_accept 2 3 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 278 (accept_3_2 1 3 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 278))) (allB_succ 2 278 (allA_succ_of_accept 1 2 278 (accept_3_2 1 2 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 278)) (allB_two
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


