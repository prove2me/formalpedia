-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch256_Segment000
-- name    : Polychromatic418967fa_Branch256_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.605826+00:00
-- url     : https://prove2.me/theorems/6be1306f-a462-44b9-b20e-2fc01ebcea3f
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

def Polychromatic418967fa.branch_256_segment_000 : allB 124 256 :=
  allB_succ 123 256 (allA_succ_of_accept 122 123 256 (accept_3_3 122 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 123 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 120 123
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 256 (accept_3_3 119 123
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 118 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 123 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 117 123 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 256 (accept_3_3 116 123 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 256 (Polychromatic418967fa.accept_12_6_3_4_1_394
  114 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 256 (accept_3_3
  113 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 256
  (Polychromatic418967fa.accept_21_7_18_4_1_5024 112 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 256 (accept_3_3 110 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 108 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 123 256 (accept_3_3 107 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 123 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 105 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 256 (accept_3_3 104 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 102 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 123 256 (accept_3_3 101 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 123 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 99 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 256 (accept_3_3 98 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 256
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 96 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 256 (accept_3_3 95 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 94 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 256 (accept_3_3 92 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 256 (accept_3_3 89 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 87 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 256 (accept_3_3 86 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 256 (accept_3_3 83 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 256 (accept_3_3 80 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 78 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 256 (accept_3_3 77 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 256 (Polychromatic418967fa.accept_17_8_4_1_1_5730 76 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 256 (accept_3_3 74 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 256
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 256 (accept_3_3 71 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 256 (accept_3_3 68 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 256 (accept_3_3 65 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 63 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 256 (accept_3_3 62 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 256
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 256 (accept_3_3 59 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 256 (accept_3_3 56 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 256 (accept_3_3 53 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 256 (accept_3_3 50 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 256 (accept_3_3 47 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 256 (accept_3_3 44 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 256 (accept_3_3 41 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 256 (accept_3_3 38 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 256
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 256 (accept_3_3 35 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 256 (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 256 (accept_3_3 32 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 256 (accept_3_3 29 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 256 (accept_3_3 26 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 256
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 256 (accept_3_3 23 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 256 (accept_3_3 20 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 256 (accept_3_3 17 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 256 (accept_3_3 14 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 256 (accept_3_3 11 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 256 (accept_3_3 8 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 256 (accept_3_3 5 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 256 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 123 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 256 (accept_3_3 2 123 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 256 (allA_of_3_1 122 122 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 256
  (allA_succ_of_accept 120 121 256 (Polychromatic418967fa.accept_22_10_11_14_1_9345 120 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 256 (accept_3_3 119 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 118 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 256 (accept_3_3 116 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 115 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 114 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 256 (accept_3_3 113 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 256 (accept_3_3 110 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 256 (Polychromatic418967fa.accept_13_5_4_9_1_601 109 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 256 (Polychromatic418967fa.accept_17_6_2_1_1_3350 108 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 256 (accept_3_3 107 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 256 (accept_3_3 104 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 103 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 102 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 256 (accept_3_3 101 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 100 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 256 (accept_3_3 98 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 97 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 256 (accept_3_3 95 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 256 (accept_3_3 92 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 256 (Polychromatic418967fa.accept_17_6_2_1_1_3350 91 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 256 (accept_3_3 89 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 256 (Polychromatic418967fa.accept_17_3_2_1_1_1367 88 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 256 (accept_3_3 86 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 85 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 84 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 256 (accept_3_3 83 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 121 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 256 (accept_3_3 80 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 79 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 256 (Polychromatic418967fa.accept_19_2_7_9_1_1114 78 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 256 (accept_3_3 77 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 121 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 256 (accept_3_3 74 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 256 (Polychromatic418967fa.accept_13_8_4_9_1_1145 73 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 256 (accept_3_3 71 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 256 (accept_3_3 68 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 256 (Polychromatic418967fa.accept_20_6_1_16_1_4059 66 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 256 (accept_3_3 65 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 256 (Polychromatic418967fa.accept_17_13_2_1_1_4483 64 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 256 (accept_3_3 62 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 256 (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 256 (accept_3_3 59 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 256 (accept_3_3 56 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 256 (accept_3_3 53 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 256 (accept_3_3 50 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 256 (Polychromatic418967fa.accept_19_11_7_9_1_8873 49 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 256 (accept_3_3 47 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 256 (accept_3_3 44 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 43 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 256 (accept_3_3 41 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 121 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 256 (accept_3_3 38 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 256 (Polychromatic418967fa.accept_19_17_7_9_1_3324 36 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 256 (accept_3_3 35 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 121 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 256 (accept_3_3 32 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 256 (Polychromatic418967fa.accept_13_5_4_9_1_601 31 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 256 (accept_3_3 29 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 256 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 256 (accept_3_3 26 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 256 (Polychromatic418967fa.accept_19_5_7_9_1_5954 24 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 256 (accept_3_3 23 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 256 (accept_3_3 20 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 256 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 256 (accept_3_3 17 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 121
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 256 (accept_3_3 14 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 256 (accept_3_3 11 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 256 (accept_3_3 8 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 256 (accept_3_3 5 121 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 256 (Polychromatic418967fa.accept_23_4_6_3_1_15634 4 121 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 256 (accept_3_3 2 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 256 (Polychromatic418967fa.accept_22_1_11_14_1_12562 1 121 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 256 (allA_succ_of_accept 119 120 256 (accept_3_3 119 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 120 256 2 59 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 120 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 117 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 256 4 29 30 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 115 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 120 256 2 57 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 120 256 (accept_3_3 113 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 120 256 8 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 120 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 111 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 256 2 55 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 109 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 256 4 27 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 256 (accept_3_3 107 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 256 2 53 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 120 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 120 256 8 13 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 103 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 256 2 51 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 256 (accept_3_3 101 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 256 4 25 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 256 (Polychromatic418967fa.accept_13_8_3_9_1_5269 99 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 256 2 49 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 97 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 256 8 12 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 256 (accept_3_3 95 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 120 256 2 47 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 120 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 93 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 256 4 23 30 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 256 2 45 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 256 (accept_3_3 89 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 256 8 11 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 256 2 43 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 256
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 85 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 256 4 21 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 256 (accept_3_3 83 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 256 2 41 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 120 256 (Polychromatic418967fa.accept_14_11_8_4_1_2628 81 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 256 8 10 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 256 2 39 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 256 (accept_3_3 77 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 256 4 19 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 120 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 120 256 2 37 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 256 8 9 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 256 (accept_3_3 71 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  120 256 2 35 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 120 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 120 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 256 4 17 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610
  67 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 256 2 33 60 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 256
  (accept_3_3 65 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 256 8 8 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 256
  (Polychromatic418967fa.accept_18_9_12_4_1_1659 63 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 256 2 31 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 256 4 15 30 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 256 (accept_3_3 59 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 256 2 29 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 256 (Polychromatic418967fa.accept_13_5_3_9_1_1189
  57 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 256 8 7 15 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 256 2 27 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 256 (accept_3_3 53 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 256 4 13 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 256 2 25 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 256
  (Polychromatic418967fa.accept_27_22_12_13_1_15633 49 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 120 256 8 6 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 120 256 (accept_3_3 47 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 256 2 23 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 256 4 11 30 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 256 2 21 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 256 (accept_3_3 41 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 256 8 5 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 256 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 120 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 256 2 19 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 37
  120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 256 4 9 30 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 256 (accept_3_3 35
  120 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 256 2 17 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 256 8 4 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 256 2 15 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 256 (accept_3_3 29 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 256 4 7 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 256 (Polychromatic418967fa.accept_18_9_12_4_1_1659 27 120
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 256 2 13 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 256 8 3 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 256 (accept_3_3 23 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  120 256 2 11 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 120 256 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 120 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 256 4 5 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19
  120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 256 2 9 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 256 (accept_3_3 17
  120 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 256 8 2 15 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 120 256 2 7 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 256 (Polychromatic418967fa.accept_19_13_6_9_1_5989 13 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 256 4 3 30 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 256 (accept_3_3 11 120 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 256 2 5 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 256
  (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 256 8 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 256 2 3 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 256 (accept_3_3 5 120 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 256 4 1 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 120 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 256 2 1 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 256 (allA_of_3_1 119 119 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 256
  (allA_succ_of_accept 117 118 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 117 118 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 256 2 58 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 256 (Polychromatic418967fa.accept_7_3_6_4_1_30
  115 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 118 256 2 57 59 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 118 256
  (accept_3_3 113 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 118 256 2 56 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 118 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 111 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 118 256 2 55 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 118 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 109 118 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 118 256 2 54 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 118 256 (accept_3_3 107 118 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 118 256 2 53 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 118 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 118 256 2 52 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 118 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 103 118 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 118 256 2 51 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 118 256 (accept_3_3 101 118 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 118 256 2 50 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 118 256
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 99 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 118 256 2 49 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 118 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 118 256 2 48 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 118 256 (accept_3_3 95 118 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 118 256 2 47 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 118 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 93
  118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 256 2 46 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 256 2 45 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 256 (accept_3_3 89 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 256 2 44 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 256 2 43 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 256 2 42 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 256 (accept_3_3 83 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 256 2 41 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 256 (Polychromatic418967fa.accept_19_5_4_9_1_4563 81 118 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 256 2 40 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 256 2 39 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 256 (accept_3_3 77 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 256 2 38 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 256 2 37 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 256 2 36 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 256 (accept_3_3 71 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 256 2 35 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 256 2 34 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 256 2 33 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 256 (accept_3_3 65 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 256 2 32 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 256 2 31 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 256 2 30 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 256 (accept_3_3 59 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 256 2 29 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 256 2 28 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 256 2 27 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 256 (accept_3_3 53 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 256 2 26 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 256 2 25 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 256 2 24 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 256 (accept_3_3 47 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 256 2 23 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 256 2 22 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 256 2 21 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 256 (accept_3_3 41 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 256 2 20 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 256 2 19 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 256 2 18 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 256 (accept_3_3 35 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 256 2 17 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 256 2 16 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 256 2 15 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 256 (accept_3_3 29 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 256 2 14 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 256 2 13 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 256 2 12 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 256 (accept_3_3 23 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 256 2 11 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 256 2 10 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 256 2 9 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 256 (accept_3_3 17 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 256 2 8 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 256 2 7 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 256 2 6 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 256 (accept_3_3 11 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 256 2 5 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 256 2 4 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 256 2 3 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 256 (accept_3_3 5 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  256 2 2 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 256 2 1 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 118 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 256 (allA_succ_of_accept 116 117 256 (accept_3_3 116 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 117 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 114 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 256 (accept_3_3 113 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 256
  (Polychromatic418967fa.accept_21_7_12_4_1_6493 112 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 256 (accept_3_3 110 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 256
  (Polychromatic418967fa.accept_19_13_3_9_1_5980 108 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 117 256 (accept_3_3 107 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 106 117 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 256 (Polychromatic418967fa.accept_17_3_15_1_1_3348 105
  117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 256 (accept_3_3 104
  117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 117 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 102 117 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 256 (accept_3_3 101 117 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 256 (accept_3_3 98 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 256 (Polychromatic418967fa.accept_27_15_9_13_1_13683 96 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 256 (accept_3_3 95 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 94 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 256 (accept_3_3 92 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 256 (accept_3_3 89 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 256 (Polychromatic418967fa.accept_15_13_12_1_1_1841 88 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 256
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 87 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 256 (accept_3_3 86 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 256 (Polychromatic418967fa.accept_17_16_15_1_1_11968 84 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 256 (accept_3_3 83 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 256 (Polychromatic418967fa.accept_19_6_3_9_1_3332 82 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 256 (accept_3_3 80 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 117 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 256 (accept_3_3 77 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 256
  (Polychromatic418967fa.accept_19_18_3_9_1_3333 75 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 256 (accept_3_3 74 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 256 (accept_3_3 71 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 70 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 256 (accept_3_3 68 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 256 (accept_3_3 65 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 256 (accept_3_3 62 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 256 (Polychromatic418967fa.accept_17_9_15_1_1_7048 60 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 256 (accept_3_3 59 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 256 (accept_3_3 56 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 256 (accept_3_3 53 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 256 (Polychromatic418967fa.accept_19_14_3_9_1_2157 52 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 256 (accept_3_3 50 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 256 (accept_3_3 47 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 256 (Polychromatic418967fa.accept_17_12_15_1_1_5798 46 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 256
  (Polychromatic418967fa.accept_21_3_12_4_1_8116 45 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 256 (accept_3_3 44 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 256 (accept_3_3 41 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 256 (Polychromatic418967fa.accept_21_19_12_4_1_8134 40 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 256
  (Polychromatic418967fa.accept_20_19_17_16_1_2732 39 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 256 (accept_3_3 38 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 256 (accept_3_3 35 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297
  34 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 256 (accept_3_3 32 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 256 (accept_3_3 29 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 256 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 256 (accept_3_3 26 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 256 (Polychromatic418967fa.accept_21_3_12_4_1_8116 24 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 256 (accept_3_3 23 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 117 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 256 (accept_3_3 20 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 256 (accept_3_3 17 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 256 (accept_3_3 14 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 256 (Polychromatic418967fa.accept_17_12_15_1_1_5798 12 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 256 (accept_3_3 11 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 117
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 256 (accept_3_3 8 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 256 (accept_3_3 5 117 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 117 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 256 (accept_3_3 2 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 256 (allA_of_3_1 116 116 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 256
  (allA_succ_of_accept 114 115 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 114 115 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 256 (accept_3_3 113 115 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 112 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 256 (accept_3_3 110 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 256 (Polychromatic418967fa.accept_24_12_19_16_1_15614 108 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 256 (accept_3_3 107 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 106 115
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 256 (accept_3_3 104 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 103 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 256 (accept_3_3 101 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 115
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 256 (accept_3_3 98 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 256 (accept_3_3 95 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 256 (accept_3_3 92 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 256 (accept_3_3 89 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 88 115 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 256 (accept_3_3 86 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 256 (accept_3_3 83 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 256 (accept_3_3 80 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 79 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 256 (accept_3_3 77 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 256 (accept_3_3 74 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 256 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 256 (accept_3_3 71 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 115
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 256 (accept_3_3 68 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 256 (Polychromatic418967fa.accept_13_2_11_9_1_591 67 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 256 (accept_3_3 65 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 256 (accept_3_3 62 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 256 (accept_3_3 59 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 256 (accept_3_3 56 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 256 (accept_3_3 53 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 52 115
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 256 (accept_3_3 50 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 256 (accept_3_3 47 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 256 (accept_3_3 44 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 256 (accept_3_3 41 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 115 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 256 (accept_3_3 38 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 256 (accept_3_3 35 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 256 (accept_3_3 32 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 256 (accept_3_3 29 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 256 (accept_3_3 26 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 256 (Polychromatic418967fa.accept_20_5_15_16_1_12727 25 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 256 (accept_3_3 23 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 256 (accept_3_3 20 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 256 (Polychromatic418967fa.accept_20_18_15_16_1_9893 18 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 256 (accept_3_3 17 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 115
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 256 (accept_3_3 14 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 256 (accept_3_3 11 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 256 (accept_3_3 8 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 256 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 256 (accept_3_3 5 115 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 115 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 256 (accept_3_3 2 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 256 (allA_succ_of_accept 113 114 256 (accept_3_3 113 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 114 256 2 56 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 114 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 114 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 256 2 55 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 109 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 256 2 54 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 256 (accept_3_3 107 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 256 2 53 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 105 114 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 256 2 52 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 103 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 256 2 51 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 256 (accept_3_3 101 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 256 2 50 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 256 2 49 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 97 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 256 2 48 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 256 (accept_3_3 95 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 256 2 47 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 256 2 46 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 91 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 256 2 45 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 256 (accept_3_3 89 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 256 2 44 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 256 2 43 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 256 2 42 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 256 (accept_3_3 83 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 256 2 41 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 256 2 40 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 256 2 39 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 256 (accept_3_3 77 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 256 2 38 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 256 2 37 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 73 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 256 2 36 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 256 (accept_3_3 71 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 256 2 35 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 256 2 34 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 256
  (Polychromatic418967fa.accept_15_7_9_1_1_473 67 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 256 2 33 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 256 (accept_3_3 65 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 256 2 32 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 256 2 31 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 256 2 30 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 256 (accept_3_3 59 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 256 2 29 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 256 2 28 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 256 2 27 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 256 (accept_3_3 53 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 256 2 26 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 256 2 25 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 256
  (Polychromatic418967fa.accept_17_15_12_1_1_3365 49 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 114 256 2 24 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 114 256 (accept_3_3 47 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 256 2 23 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 256 2 22 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 256 2 21 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 256 (accept_3_3 41 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 256 2 20 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 256 2 19 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 256 2 18 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 256 (accept_3_3 35 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 256 2 17 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 256 2 16 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 256
  (Polychromatic418967fa.accept_24_7_18_16_1_12162 31 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 114 256 2 15 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 114 256 (accept_3_3 29 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 256 2 14 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 256 2 13 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 256 2 12 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 256 (accept_3_3 23 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 256 2 11 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 256 2 10 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 256 2 9 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 256 (accept_3_3 17 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 256 2 8 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 256 2 7 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 256 2 6 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 256 (accept_3_3 11 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 256 2 5 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 256 2 4 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 256 2 3 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 256 (accept_3_3 5 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114
  256 2 2 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  114 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 114 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 114 256 2 1 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 114 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 114 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 256 (allA_of_3_1 113 113 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 256
  (allA_succ_of_accept 111 112 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 111 112 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 256 2 55 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 256
  (Polychromatic418967fa.accept_17_7_10_1_1_4488 109 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 112 256 4 27 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 112 256 (accept_3_3 107 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 112 256 2 53 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 112 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 105 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 112 256 8 13 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 112 256
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 103 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 112 256 2 51 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 112 256 (accept_3_3 101 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 112 256 4 25 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 112 256 (Polychromatic418967fa.accept_15_9_7_1_1_1075 99 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 256 2 49 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 256
  (Polychromatic418967fa.accept_19_2_17_9_1_10317 97 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 112 256 16 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 112 256 (accept_3_3 95 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 112 256 2 47 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 112 256 (Polychromatic418967fa.accept_23_1_20_3_1_12357 93 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 256 4 23 28 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 112 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 112 256 2 45 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 112 256 (accept_3_3 89 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 112 256 8 11 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 112 256 (Polychromatic418967fa.accept_19_11_17_9_1_10138 87 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 256 2 43 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 256
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 85 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 256 4 21 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 256 (accept_3_3 83 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 256 2 41 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 112 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 256 16 5 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 256
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 79 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 256 2 39 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 256 (accept_3_3 77 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 256 4 19 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 256 (Polychromatic418967fa.accept_17_7_10_1_1_4488 75 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 256 2 37 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 256
  (Polychromatic418967fa.accept_27_19_4_13_1_15632 73 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 112 256 8 9 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 112 256 (accept_3_3 71 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 256 2 35 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 69 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 256 4 17 28 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 67 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 112 256 2 33 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 112 256 (accept_3_3 65 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 256 16 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 112 256 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 112 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 256 2 31 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 256 (Polychromatic418967fa.accept_10_1_2_6_1_638
  61 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 256 4 15 28 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 256
  (accept_3_3 59 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 256 2 29 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 256
  (Polychromatic418967fa.accept_29_28_25_24_1_15631 57 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 112 256 8 7 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 112 256 (Polychromatic418967fa.accept_13_3_8_9_1_1134 55 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 256 2 27 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 256 (accept_3_3 53 112 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 256 4 13 28 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 112 256 2 25 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 112 256 (Polychromatic418967fa.accept_19_11_17_9_1_10138 49 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 112 256 16 3 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 256 (accept_3_3 47 112 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 256 2 23 56 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 256 4 11 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 43 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 256 2 21 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 256 (accept_3_3 41 112 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 256 8 5 14 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 256
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 256 2 19 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 256 (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 256 4 9 28 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 256 (accept_3_3 35 112 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 256 2 17 56 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 256
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 256 16 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 256 2 15 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 256 (accept_3_3 29 112 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 256 4 7 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 112
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 256 2 13 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 256
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 256 8 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 256 (accept_3_3 23 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 256 2 11 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 112 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 112 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 256 4 5 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 256 (Polychromatic418967fa.accept_21_19_7_4_1_4994
  19 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 256 2 9 56 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 256
  (accept_3_3 17 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 256 16 1 7 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 256
  (Polychromatic418967fa.accept_23_15_20_3_1_13910 15 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 256 2 7 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 256 (Polychromatic418967fa.accept_19_13_17_9_1_3312 13 112 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 256 4 3 28 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 256 (accept_3_3 11
  112 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 256 2 5 56 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 256
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 256 8 1 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 112 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 256 2 3 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 256 (accept_3_3 5 112 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 256 4 1 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 112 256 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 112 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 256 2 1 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 112 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 256 (allA_succ_of_accept 110 111 256 (accept_3_3 110 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 111
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 256 (accept_3_3 107 111
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 106 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 256 (accept_3_3 104 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 256 (Polychromatic418967fa.accept_10_2_1_6_1_634
  102 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 256 (accept_3_3
  101 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 100 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 111 256 (Polychromatic418967fa.accept_13_8_7_9_1_611 99 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 256 (accept_3_3 98 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 256 (Polychromatic418967fa.accept_7_5_6_4_1_117
  96 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 256 (accept_3_3 95
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 94 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 111 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 256 (accept_3_3 92 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 256 (Polychromatic418967fa.accept_11_2_1_3_1_683
  90 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 256 (accept_3_3 89
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 88 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 256 (accept_3_3 86 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 256 (Polychromatic418967fa.accept_13_6_7_9_1_1848
  84 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 256 (accept_3_3 83
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 82 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 111 256 (Polychromatic418967fa.accept_13_3_7_9_1_1153 81 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 256 (accept_3_3 80 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477
  78 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 256 (accept_3_3 77
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 256
  (Polychromatic418967fa.accept_13_11_7_9_1_612 76 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 111 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 256 (accept_3_3 74 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 256 (accept_3_3 71
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 70 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 256 (accept_3_3 68 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 66
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 256 (accept_3_3 65
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 111 256 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 256 (accept_3_3 62 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477
  60 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 256 (accept_3_3 59
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 58 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 111 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 256 (accept_3_3 56 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 256 (Polychromatic418967fa.accept_7_5_6_4_1_117
  54 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 256 (accept_3_3 53
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 52 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 111 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 256 (accept_3_3 50 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834
  48 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 256 (accept_3_3 47
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 46 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 256 (accept_3_3 44 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477
  42 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 256 (accept_3_3 41
  111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 111 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 256 (accept_3_3 38 111 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 256
  (Polychromatic418967fa.accept_21_15_6_4_1_4990 36 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 256 (accept_3_3 35 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 256 (accept_3_3 32 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 256 (accept_3_3 29 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 256 (accept_3_3 26 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 256 (accept_3_3 23 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 256 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 256 (accept_3_3 20 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 256 (accept_3_3 17 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 256 (accept_3_3 14 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 256 (accept_3_3 11 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 256 (accept_3_3 8 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 256 (accept_3_3 5 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 111 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 256 (accept_3_3 2 111 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 256 (allA_of_3_1 110 110 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 256
  (allA_succ_of_accept 108 109 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 108 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 256 (accept_3_3 107 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 256 (accept_3_3 104 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 103 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 256 (accept_3_3 101 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 256 (Polychromatic418967fa.accept_19_5_14_9_1_4554 100
  109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 256 (accept_3_3 98 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 256 (accept_3_3 95 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 256 (accept_3_3 92 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 91 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 256 (Polychromatic418967fa.accept_20_10_9_16_1_8518 90 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 256 (accept_3_3 89 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 256 (accept_3_3 86 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 256 (accept_3_3 83 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 256 (accept_3_3 80 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 256 (accept_3_3 77 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 256 (Polychromatic418967fa.accept_17_8_7_1_1_4521 76 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 256 (accept_3_3 74 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 73 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 256 (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 256 (accept_3_3 71 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 256 (accept_3_3 68 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 256 (accept_3_3 65 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 64 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 256 (accept_3_3 62 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 256 (accept_3_3 59 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 256 (accept_3_3 56 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 256 (accept_3_3 53 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 256 (accept_3_3 50 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 49 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 256 (accept_3_3 47 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 256 (accept_3_3 44 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 256 (accept_3_3 41 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 256 (accept_3_3 38 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 256 (Polychromatic418967fa.accept_22_15_21_14_1_14041 37 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 256 (accept_3_3 35 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217
  34 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 256 (accept_3_3 32 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 256 (Polychromatic418967fa.accept_19_12_14_9_1_10229 31 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 256 (accept_3_3 29 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 109
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 256 (accept_3_3 26 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 256 (accept_3_3 23 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 256 (accept_3_3 20 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 256 (Polychromatic418967fa.accept_20_19_9_16_1_2744 19 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 256 (accept_3_3 17 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 256 (accept_3_3 14 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 256 (accept_3_3 11 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 256 (accept_3_3 8 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 256 (accept_3_3 5 109 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 109 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 256 (accept_3_3 2 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 109 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 256 (allA_succ_of_accept 107 108 256 (accept_3_3 107 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 108 256 2 53 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 108 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 105 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 256 4 26 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 103 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 256 2 51 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 256 (accept_3_3 101 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 108 256 4 25 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 108 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 256 2 49 54 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 97 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 256 4 24 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 256 (accept_3_3 95 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 256 2 47 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 93 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 256 4 23 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 91 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 256 2 45 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 256 (accept_3_3 89 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 256 4 22 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 256 (Polychromatic418967fa.accept_17_2_6_1_1_8357 87 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 256 2 43 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 85 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 256 4 21 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 256 (accept_3_3 83 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 256 2 41 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 256 4 20 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 256
  (Polychromatic418967fa.accept_15_4_3_1_1_487 79 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 256 2 39 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 256 (accept_3_3 77 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 256 4 19 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 256 (Polychromatic418967fa.accept_19_18_13_9_1_5971 75 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 256 2 37 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 256 4 18 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 256 (accept_3_3 71 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 256 2 35 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 256 4 17 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 256
  (Polychromatic418967fa.accept_19_10_13_9_1_4552 67 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 108 256 2 33 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 108 256 (accept_3_3 65 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 256 4 16 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 256 2 31 54 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 61 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 256 4 15 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 256 (accept_3_3 59 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 256 2 29 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 256 4 14 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 256 2 27 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 256 (accept_3_3 53 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 256 4 13 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 256 2 25 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 256 4 12 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 256 (accept_3_3 47 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 256 2 23 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 256 4 11 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 256 2 21 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 256 (accept_3_3 41 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 256 4 10 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 256 2 19 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 256
  (Polychromatic418967fa.accept_17_3_6_1_1_8382 37 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 256 4 9 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 256 (accept_3_3 35 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  108 256 2 17 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 108 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 256 4 8 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 256 (Polychromatic418967fa.accept_13_5_4_9_1_601
  31 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 256 2 15 54 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 256
  (accept_3_3 29 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 256 4 7 27 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 256 2 13 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 256 (Polychromatic418967fa.accept_19_6_13_9_1_3291 25 108 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 256 4 6 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 256 (accept_3_3 23 108 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 256 2 11 54 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 256
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 256 4 5 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 108 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 256 2 9 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 256 (accept_3_3 17 108 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 256 4 4 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 256 2 7 54 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 256 4 3 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 256 (accept_3_3 11 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  108 256 2 5 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 256 (Polychromatic418967fa.accept_22_9_20_14_1_9412 9 108 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 256 4 2 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 256 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 108 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 256 2 3 54 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 256 (accept_3_3 5
  108 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 256 4 1 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 256 2 1 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 256 (allA_of_3_1 107 107 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 256
  (allA_succ_of_accept 105 106 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 106 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 256 2 52 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 256 (Polychromatic418967fa.accept_7_5_1_4_1_122
  103 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 106 256 2 51 53 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 106 256
  (accept_3_3 101 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 106 256 2 50 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 106 256
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 99 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 106 256 2 49 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 106 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 97 106 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 106 256 2 48 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 106 256 (accept_3_3 95 106 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 106 256 2 47 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 106 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 93 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 106 256 2 46 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 106 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 106 256 2 45 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 106 256 (accept_3_3 89 106 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 106 256 2 44 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 106 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 87
  106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 256 2 43 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 256 2 42 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 256 (accept_3_3 83 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 256 2 41 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 256 2 40 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 256 2 39 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 256 (accept_3_3 77 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 256 2 38 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 256 2 37 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 256 2 36 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 256 (accept_3_3 71 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 256 2 35 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 256 2 34 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 256 2 33 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 256 (accept_3_3 65 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 256 2 32 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 256 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 106 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 256 2 31 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 256 2 30 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 256 (accept_3_3 59 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 256 2 29 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 256 2 28 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 256 2 27 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 256 (accept_3_3 53 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 256 2 26 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 256 2 25 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 256 2 24 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 256 (accept_3_3 47 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 256 2 23 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 256 2 22 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 256
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 256 2 21 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 256 (accept_3_3 41 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 256 2 20 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 256 2 19 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 256 2 18 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 256 (accept_3_3 35 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 256 2 17 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 256 2 16 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 256 2 15 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 256 (accept_3_3 29 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 256 2 14 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 106 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 256 2 13 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 256 2 12 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 256 (accept_3_3 23 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 256 2 11 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 256 2 10 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 256 2 9 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 256 (accept_3_3 17 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 256 2 8 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 256 2 7 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 256 2 6 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 256 (accept_3_3 11 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 256 2 5 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 256 (Polychromatic418967fa.accept_23_9_14_3_1_5608 9 106 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 256 2 4 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 256 2 3 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 256 (accept_3_3 5 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  256 2 2 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 256 2 1 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 256 (allA_succ_of_accept 104 105 256 (accept_3_3 104 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 105
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 256 (accept_3_3 101 105
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 100 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 99 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 256 (accept_3_3 98 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 256 (Polychromatic418967fa.accept_11_8_6_3_1_661
  96 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 256 (accept_3_3 95
  105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 94 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 256 (accept_3_3 92 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 256 (Polychromatic418967fa.accept_12_6_9_4_1_96
  90 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 256 (accept_3_3 89
  105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 88 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 105 256 (Polychromatic418967fa.accept_14_3_7_4_1_118 87 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 256 (accept_3_3 86 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210
  84 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 256 (accept_3_3 83
  105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 82 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 105 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 256 (accept_3_3 80 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 256 (Polychromatic418967fa.accept_12_6_9_4_1_96
  78 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 256 (accept_3_3 77
  105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 256
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 76 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 256 (accept_3_3 74 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 256
  (Polychromatic418967fa.accept_19_15_10_9_1_5956 72 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 256 (accept_3_3 71 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 105 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 105 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 105
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 256 (accept_3_3 68 105
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 256 (accept_3_3 65 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 256 (accept_3_3 62 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 256
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 256 (accept_3_3 59 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 256 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 256 (accept_3_3 56 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 256 (accept_3_3 53 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 256 (accept_3_3 50 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 256 (accept_3_3 47 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 256 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 256 (accept_3_3 44 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 256 (accept_3_3 41 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 256 (Polychromatic418967fa.accept_17_6_3_1_1_7011 40 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 256 (accept_3_3 38 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 256
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 256 (accept_3_3 35 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 256 (Polychromatic418967fa.accept_23_10_13_3_1_15630 33 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 256 (accept_3_3 32 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 256 (accept_3_3 29 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 256 (Polychromatic418967fa.accept_18_9_15_4_1_5173 27 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 256 (accept_3_3 26 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 256 (accept_3_3 23 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 256 (Polychromatic418967fa.accept_19_3_10_9_1_7338 22 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 256 (accept_3_3 20 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 256 (accept_3_3 17 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 256 (accept_3_3 14 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 256 (accept_3_3 11 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 256 (accept_3_3 8 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 256 (accept_3_3 5 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 105 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 256 (accept_3_3 2 105 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 256 (allA_of_3_1 104 104 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 256
  (allA_succ_of_accept 102 103 256 (Polychromatic418967fa.accept_15_12_13_1_1_3695 102 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 256 (accept_3_3 101 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 256 (accept_3_3 98 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 256 (Polychromatic418967fa.accept_19_1_8_9_1_3304 96 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 256 (accept_3_3 95 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 103
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 256 (accept_3_3 92 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 256 (Polychromatic418967fa.accept_21_7_19_4_1_4956 91 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 256 (accept_3_3 89 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 256 (accept_3_3 86 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 84 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 256 (accept_3_3 83 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 103
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 256 (accept_3_3 80 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 256 (accept_3_3 77 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 256 (accept_3_3 74 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 73 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 256 (accept_3_3 71 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 256 (accept_3_3 68 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 67 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 256 (Polychromatic418967fa.accept_24_18_7_16_1_15629 66 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 256 (accept_3_3 65 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 103 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 256 (accept_3_3 62 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 61 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 256 (Polychromatic418967fa.accept_13_8_12_9_1_1168 60 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 256 (accept_3_3 59 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 103 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 256 (accept_3_3 56 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 256 (Polychromatic418967fa.accept_19_16_8_9_1_8858 54 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 256 (accept_3_3 53 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 256 (Polychromatic418967fa.accept_19_14_8_9_1_4547 52 103
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 256 (accept_3_3 50 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 256 (accept_3_3 47 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 256 (accept_3_3 44 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 256 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 256 (accept_3_3 41 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 103
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 256 (accept_3_3 38 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 256 (accept_3_3 35 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 256 (accept_3_3 32 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 256 (Polychromatic418967fa.accept_21_10_19_4_1_8121 31 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 256 (accept_3_3 29 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 256 (accept_3_3 26 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 256 (Polychromatic418967fa.accept_27_24_22_13_1_15628 24 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 256 (accept_3_3 23 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 256 (accept_3_3 20 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 256 (accept_3_3 17 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 256 (accept_3_3 14 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 256 (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 256 (accept_3_3 11 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 103
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 256 (accept_3_3 8 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 256 (accept_3_3 5 103 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 256 (Polychromatic418967fa.accept_19_4_8_9_1_10211 4 103 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 256 (accept_3_3 2 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 256 (allA_succ_of_accept 101 102 256 (accept_3_3 101 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 256 2 50 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 256 2 49 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 97 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 256 2 48 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 256 (accept_3_3 95 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 256 2 47 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 256 2 46 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 256 2 45 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 256 (accept_3_3 89 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 256 2 44 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 256 2 43 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 256
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 85 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 256 2 42 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 256 (accept_3_3 83 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 256 2 41 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 256 2 40 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 256 2 39 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 256 (accept_3_3 77 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 256 2 38 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 256 2 37 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 256 2 36 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 256 (accept_3_3 71 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 256 2 35 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 256 2 34 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 67 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 256 2 33 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 256 (accept_3_3 65 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 256 2 32 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 256 2 31 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 256 2 30 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 256 (accept_3_3 59 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 256 2 29 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 256 2 28 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 256 2 27 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 256 (accept_3_3 53 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 256 2 26 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 256 2 25 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 256
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 256 2 24 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 256 (accept_3_3 47 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 256 2 23 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 256 2 22 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 256 2 21 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 256 (accept_3_3 41 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 256 2 20 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 256 2 19 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 256 2 18 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 256 (accept_3_3 35 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 256 2 17 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 256 2 16 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 256 2 15 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 256 (accept_3_3 29 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 256 2 14 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 256 2 13 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 256 2 12 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 256 (accept_3_3 23 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 256 2 11 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 256 2 10 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 256 2 9 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 256 (accept_3_3 17 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 256 2 8 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 256 2 7 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 256
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 102 256 2 6 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 102 256 (accept_3_3 11 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 256 2 5 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 256 2 4 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 256 2 3 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 256 (accept_3_3 5 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  256 2 2 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 256 2 1 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 102 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 256 (allA_of_3_1 101 101 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 256 (allA_succ_of_accept 99
  100 256 (Polychromatic418967fa.accept_15_9_10_1_1_1062 99 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 256 2 49 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 97 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 256 4 24 25 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 100 256 (accept_3_3 95 100 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 100 256 2 47 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 256 4 23 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 256 (Polychromatic418967fa.accept_19_15_5_9_1_3299 91 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 256 2 45 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 256 (accept_3_3 89 100 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 256 4 22 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 256 2 43 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 100 256 (Polychromatic418967fa.accept_18_13_10_4_1_5150 85 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 100 256 4 21 25 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 256 (accept_3_3 83 100 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 100 256 2 41 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 100 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 100 256 4 20 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 100 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 100 256 2 39 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 100 256 (accept_3_3 77 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 100 256 4 19 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 100 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75
  100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 256 2 37 50 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 256
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 100 256 4 18 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 100 256 (accept_3_3 71 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 256 2 35 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 256 4 17 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 256
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 256 2 33 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 256 (accept_3_3 65 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 256 4 16 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 256 (Polychromatic418967fa.accept_17_12_15_1_1_5798 63 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 256 2 31 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 256 4 15 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 256 (accept_3_3 59 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 256 2 29 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 256 4 14 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 256 2 27 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 256 (accept_3_3 53 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 256 4 13 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 256 2 25 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 256
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 49 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 100 256 4 12 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 100 256 (accept_3_3 47 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 256 2 23 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 256 (Polychromatic418967fa.accept_19_7_5_9_1_10202 45 100 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 256 4 11 25 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 256 2 21 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 256 (accept_3_3 41 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 256 4 10 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 256 2 19 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 256
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 256 4 9 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 100 256 (accept_3_3 35 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  100 256 2 17 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 100 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 100 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 256 4 8 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 256
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 100 256 2 15 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 100 256 (accept_3_3 29 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 256 4 7 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 100 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 100 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 256 2 13 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 256 4 6 25 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 256 (accept_3_3 23
  100 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 256 2 11 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 256 4 5 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 256 2 9 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 256 (accept_3_3 17 100 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 256 4 4 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 100 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 256 2 7 50 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 256 4 3 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 100 256 (accept_3_3 11 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 256 2 5 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 100 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 100 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 256 4 2 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 256 2 3 50 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 256 (accept_3_3 5
  100 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 256 4 1 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 100 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 100 256 2 1 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 100 256 (Polychromatic418967fa.accept_19_1_5_9_1_10341 1 100 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 100
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  256 (allA_succ_of_accept 98 99 256 (accept_3_3 98 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 256 (accept_3_3 95 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 93 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 256 (accept_3_3 92 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 256 (accept_3_3 89 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 256 (Polychromatic418967fa.accept_23_19_7_3_1_5594 88 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 256 (accept_3_3 86 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 256 (Polychromatic418967fa.accept_18_12_9_4_1_2740 84 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 256 (accept_3_3 83 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 99 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 256
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 81 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 256 (accept_3_3 80 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 78 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 256 (accept_3_3 77 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 256 (Polychromatic418967fa.accept_13_11_8_9_1_1161 76 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 256 (accept_3_3 74 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 256 (accept_3_3 71 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 256 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 256
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 69 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 256 (accept_3_3 68 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 256 (accept_3_3 65 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 256 (Polychromatic418967fa.accept_13_12_8_9_1_1833 64 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 256 (accept_3_3 62 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 256 (Polychromatic418967fa.accept_23_14_7_3_1_10784 60 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 256 (accept_3_3 59 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 256 (Polychromatic418967fa.accept_24_10_3_16_1_2036 58 99
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 256
  (Polychromatic418967fa.accept_20_17_19_16_1_6996 57 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 256 (accept_3_3 56 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 256 (accept_3_3 53 99 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52
  99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 256
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 256 (accept_3_3 50 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 256 (Polychromatic418967fa.accept_18_12_9_4_1_2740 48 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 256 (accept_3_3 47 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 46 99 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 256 (accept_3_3 44 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 256 (accept_3_3 41 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 256
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 256 (accept_3_3 38 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 256 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 256 (accept_3_3 35 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 256 (Polychromatic418967fa.accept_19_15_4_9_1_11608 34 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 256 (accept_3_3 32 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 256 (accept_3_3 29 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 256 (Polychromatic418967fa.accept_24_4_3_16_1_2035 28 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 256
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 256 (accept_3_3 26 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 256 (accept_3_3 23 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 256 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 256 (accept_3_3 20 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 256 (accept_3_3 17 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 256 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 256
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 256 (accept_3_3 14 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 256 (accept_3_3 11 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 256
  (Polychromatic418967fa.accept_20_9_19_16_1_11366 9 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 256 (accept_3_3 8 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 256 (accept_3_3 5 99 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 99 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  99 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 256 (accept_3_3 2 99 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  256 (allA_of_3_1 98 98 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 256 (allA_succ_of_accept 96 97 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 256 (accept_3_3 95 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 256 (accept_3_3 92 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 256
  (Polychromatic418967fa.accept_21_6_13_4_1_6521 90 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 256 (accept_3_3 89 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 256 (Polychromatic418967fa.accept_13_10_6_9_1_1152 88 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 256 (accept_3_3 86 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 256 (Polychromatic418967fa.accept_13_7_6_9_1_1831 85 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 256 (accept_3_3 83 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 256 (accept_3_3 80 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 256 (accept_3_3 77 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 256 (Polychromatic418967fa.accept_27_22_16_13_1_13701 76 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 256 (accept_3_3 74 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 256 (accept_3_3 71 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 256 (accept_3_3 68 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 256 (accept_3_3 65 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 256 (accept_3_3 62 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 256 (accept_3_3 59 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 256 (accept_3_3 56 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 256 (accept_3_3 53 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 256 (accept_3_3 50 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 256 (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 256 (accept_3_3 47 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 256 (accept_3_3 44 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 256 (accept_3_3 41 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 256 (accept_3_3 38 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 256
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 256 (accept_3_3 35 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 256 (accept_3_3 32 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 256 (accept_3_3 29 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 256 (accept_3_3 26 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 256 (accept_3_3 23 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 256 (accept_3_3 20 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 256
  (Polychromatic418967fa.accept_19_18_2_9_1_8870 18 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 256 (accept_3_3 17 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 256 (accept_3_3 14 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 256 (accept_3_3 11 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 256 (accept_3_3 8 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 256 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 256 (accept_3_3 5 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  256 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 97 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 256 (accept_3_3 2 97 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 256
  (allA_succ_of_accept 95 96 256 (accept_3_3 95 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  256 2 47 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 256 4 23 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 256 2 45 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 256 (accept_3_3 89 96 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 256 8 11 12 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 256
  (Polychromatic418967fa.accept_18_15_6_4_1_5147 87 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 256 2 43 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 256 4 21 24 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 256 (accept_3_3 83 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 256 2 41 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285
  81 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 256 16 5 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 256 2 39 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 256 (accept_3_3 77 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 256 4 19 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 256 2 37 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 73
  96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 256 8 9 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 256 (accept_3_3 71
  96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 256 2 35 48 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 256 4 17 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 96 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 256 2 33 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 256 (accept_3_3 65 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 256 32 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 256 2 31 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 256 4 15 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 256 (accept_3_3 59 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96
  256 2 29 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 96 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 96 256 8 7 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 256 2 27 48 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 256 (accept_3_3 53 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 256 4 13 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51
  96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 256 2 25 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 256 16 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 256 (accept_3_3 47 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96
  256 2 23 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 96 256 (Polychromatic418967fa.accept_21_3_12_4_1_8116 45 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 96 256 4 11 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 96 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 256 2 21 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 256 (accept_3_3 41 96 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 256 8 5 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 256 2 19 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 256 4 9 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 256 (accept_3_3 35 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  256 2 17 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 96 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 256 32 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 256 (Polychromatic418967fa.accept_19_12_1_9_1_10281 31 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 256 2 15 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 256 (accept_3_3 29 96 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 256 4 7 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 256 2 13 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 256 8 3 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 256 (accept_3_3 23 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  256 2 11 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 96 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 256 4 5 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 256 2 9 48 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 256 (accept_3_3 17 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 256 16 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 256 2 7 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 256 4 3 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 256 (accept_3_3 11 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  256 2 5 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 256 8 1 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 256 2 3 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 256 (accept_3_3 5 96 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 256 4 1 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 256 2 1 48 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 256 (allA_of_3_1 95 95 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 256
  (allA_succ_of_accept 93 94 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 93 94 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 256 2 46 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 256 (Polychromatic418967fa.accept_12_7_10_4_1_382
  91 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 256 2 45 47 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 256
  (accept_3_3 89 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 256 2 44 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 256
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 87 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 256 2 43 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 94 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 256 2 42 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 256 (accept_3_3 83 94 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 256 2 41 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 256 (Polychromatic418967fa.accept_19_5_18_9_1_8830
  81 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 256 2 40 47 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 256 2 39 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 256 (accept_3_3 77 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 256 2 38 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 256 2 37 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 256 2 36 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 256 (accept_3_3 71 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 256 2 35 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 256 2 34 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 256 2 33 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 256 (accept_3_3 65 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 256 2 32 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 256 2 31 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 256 2 30 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 256 (accept_3_3 59 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 256 2 29 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 256 2 28 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 256 2 27 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 256 (accept_3_3 53 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 256 2 26 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 256 (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 256 2 25 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 256 2 24 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 256 (accept_3_3 47 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 256 2 23 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 256 2 22 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 256 2 21 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 256 (accept_3_3 41 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 256 2 20 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 256 (Polychromatic418967fa.accept_25_14_19_6_1_15627 39 94 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 256 2 19 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 256 2 18 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 256 (accept_3_3 35 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 256 2 17 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 256 2 16 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 256 2 15 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 256 (accept_3_3 29 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 256 2 14 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 256 2 13 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 256 2 12 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 256 (accept_3_3 23 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 256 2 11 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 256 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 256 2 10 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 256
  (Polychromatic418967fa.accept_11_8_6_3_1_661 19 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 256 2 9 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 256 (accept_3_3 17 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  256 2 8 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 256 2 7 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 94 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 256 2 6 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 256 (accept_3_3 11 94 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 256 2 5 47 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 94 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 256 2 4 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 256 2 3 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 256 (accept_3_3 5 94 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 256 2 2 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 94 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 256 2 1 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 256
  (allA_succ_of_accept 92 93 256 (accept_3_3 92 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 256 (accept_3_3 89 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 256 (accept_3_3 86 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 256 (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 256 (accept_3_3 83 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 256
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 256 (accept_3_3 80 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 256 (accept_3_3 77 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 256 (accept_3_3 74 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 256 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 256 (accept_3_3 71 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 256 (accept_3_3 68 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 256 (accept_3_3 65 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 256 (accept_3_3 62 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 256 (accept_3_3 59 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 256
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 256 (accept_3_3 56 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 256 (accept_3_3 53 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 256 (accept_3_3 50 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 256 (accept_3_3 47 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 256
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 256 (accept_3_3 44 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 256 (accept_3_3 41 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 256
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 256 (accept_3_3 38 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 256 (accept_3_3 35 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 256 (accept_3_3 32 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 256 (accept_3_3 29 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 256 (accept_3_3 26 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 256 (accept_3_3 23 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 256 (Polychromatic418967fa.accept_24_22_21_16_1_15626 22 93 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 256
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 256 (accept_3_3 20 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 256 (accept_3_3 17 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 256 (accept_3_3 14 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 256 (accept_3_3 11 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 93 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 256
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 256 (accept_3_3 8 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 256 (accept_3_3 5 93 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 256 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 93 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3
  93 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 256 (accept_3_3 2 93 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 256
  (allA_of_3_1 92 92 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 256 (allA_succ_of_accept 90 91 256
  (Polychromatic418967fa.accept_17_5_6_1_1_5735 90 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 256 (accept_3_3 89 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 256 (accept_3_3 86 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 85 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 256 (accept_3_3 83 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 256 (accept_3_3 80 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 256 (accept_3_3 77 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 256 (Polychromatic418967fa.accept_21_13_7_4_1_4991 76 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 256 (accept_3_3 74 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 256 (Polychromatic418967fa.accept_14_3_7_4_1_118 73 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 256 (accept_3_3 71 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 256 (accept_3_3 68 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 256 (accept_3_3 65 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 256 (Polychromatic418967fa.accept_21_1_7_4_1_4947 64 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 256 (accept_3_3 62 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 256 (accept_3_3 59 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 256 (accept_3_3 56 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 256
  (Polychromatic418967fa.accept_17_3_6_1_1_8382 54 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 256 (accept_3_3 53 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 256 (accept_3_3 50 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 256 (Polychromatic418967fa.accept_19_11_15_9_1_6002 49 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 256 (accept_3_3 47 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 256 (accept_3_3 44 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 256 (accept_3_3 41 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 256 (Polychromatic418967fa.accept_19_2_15_9_1_7318 40 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 256 (accept_3_3 38 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 256
  (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 256 (accept_3_3 35 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 256 (accept_3_3 32 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 256 (Polychromatic418967fa.accept_14_3_7_4_1_118 31 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 256 (accept_3_3 29 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 256 (Polychromatic418967fa.accept_22_6_3_14_1_9379 28 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 256 (accept_3_3 26 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 256 (accept_3_3 23 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 256 (accept_3_3 20 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 256 (Polychromatic418967fa.accept_17_2_6_1_1_8357 19 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 256
  (Polychromatic418967fa.accept_19_18_15_9_1_3310 18 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 256 (accept_3_3 17 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 256 (accept_3_3 14 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 256 (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 256 (accept_3_3 11 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 256 (accept_3_3 8 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 256 (accept_3_3 5 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  256 (Polychromatic418967fa.accept_19_4_15_9_1_8845 4 91 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 256 (accept_3_3 2 91 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 256 (Polychromatic418967fa.accept_20_1_11_16_1_699 1 91 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 256
  (allA_succ_of_accept 89 90 256 (accept_3_3 89 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  256 2 44 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 256 2 43 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 90 256 (Polychromatic418967fa.accept_20_5_10_16_1_9890 85 90 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 256 2 42 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 256 (accept_3_3 83 90 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 256 2 41 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 81 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 256 2 40 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 256 2 39 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 256 (accept_3_3 77 90 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 256 2 38 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75
  90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 256 2 37 45 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 256 2 36 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 256 (accept_3_3 71 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 256 2 35 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 90 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 256 2 34 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 67 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 256 2 33 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 256 (accept_3_3 65 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 90 256 2 32 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 90 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 256 2 31 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 256 2 30 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 256 (accept_3_3 59 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 256 2 29 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 256 2 28 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 256
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 55 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 256 2 27 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 256 (accept_3_3 53 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 256 2 26 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 90 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 256 2 25 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 256
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 256 2 24 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 256 (accept_3_3 47 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 256 2 23 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 90 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 256 2 22 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 256
  (Polychromatic418967fa.accept_19_5_14_9_1_4554 43 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 256 2 21 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 256 (accept_3_3 41 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 256 2 20 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 90 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 256 2 19 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 256 2 18 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 256 (accept_3_3 35 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 256 2 17 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 90 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 256 2 16 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 256 2 15 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 256 (accept_3_3 29 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 256 2 14 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 90 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 256 2 13 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 256
  (Polychromatic418967fa.accept_19_6_14_9_1_8863 25 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 256 2 12 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 256 (accept_3_3 23 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 256 2 11 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 90 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 256 2 10 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 256 2 9 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 256 (accept_3_3 17 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90
  256 2 8 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  90 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 90 256 2 7 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 90 256 (Polychromatic418967fa.accept_21_13_6_4_1_2178 13 90 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 256 2 6 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 256 (accept_3_3 11 90 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 256 2 5 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 256 2 4 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 256 (Polychromatic418967fa.accept_21_7_6_4_1_3445 7 90 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 256 2 3 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 256 (accept_3_3 5 90 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 256 2 2 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 256 2 1 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 1
  90 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 256
  (allA_of_3_1 89 89 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 256 (allA_succ_of_accept 87 88 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 256 2 43 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 88 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 256 4 21 22 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 256 (accept_3_3 83 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 256 2 41 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 256
  (Polychromatic418967fa.accept_19_5_12_9_1_4588 81 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 88 256 8 10 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 88 256 (Polychromatic418967fa.accept_13_1_10_9_1_215 79 88 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 256 2 39 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 88 256 (accept_3_3 77 88 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88 256 4 19 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 256 2 37 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 256 8 9 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 88 256 (accept_3_3 71 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88
  256 2 35 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  69 88 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 88 256 4 17 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 88 256 (Polychromatic418967fa.accept_19_10_12_9_1_10150 67 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 256 2 33 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 256 (accept_3_3 65 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 256 8 8 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63
  88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 256 2 31 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 256
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 61 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 256 4 15 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 256 (accept_3_3 59 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  256 2 29 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 88 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 256 8 7 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 88 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 88 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 256 2 27 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 256 (accept_3_3 53 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 256 4 13 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51
  88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 256 2 25 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 256
  (Polychromatic418967fa.accept_17_15_3_1_1_9696 49 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 256 8 6 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 256 (accept_3_3 47 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88
  256 2 23 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 88 256 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 88 256 4 11 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 88 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 256 2 21 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 256 (accept_3_3 41 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 256 8 5 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39
  88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 256 2 19 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 256 4 9 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 256 (accept_3_3 35 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  256 2 17 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 88 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 256 8 4 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 256 (Polychromatic418967fa.accept_27_4_7_13_1_15625 31 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 256 2 15 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 256 (accept_3_3 29 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 256 4 7 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 256 (Polychromatic418967fa.accept_13_1_10_9_1_215
  27 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 256 2 13 44 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 256
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 256 8 3 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 256 (accept_3_3 23 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  256 2 11 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 88 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 256 4 5 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 256 2 9 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 256 (accept_3_3 17 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 256 8 2 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 88 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 256 2 7 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 256 4 3 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 256 (accept_3_3 11 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  256 2 5 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 256 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 256 8 1 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 256 (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 88 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 256 2 3 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 256 (accept_3_3 5 88 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 256 4 1 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 256 2 1 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  256 (allA_succ_of_accept 86 87 256 (accept_3_3 86 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 256 (accept_3_3 83 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 256 (accept_3_3 80 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 256 (accept_3_3 77 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 256 (accept_3_3 74 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 256 (Polychromatic418967fa.accept_19_15_11_9_1_11629 72 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 256 (accept_3_3 71 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 87 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 256 (accept_3_3 68 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 256 (accept_3_3 65 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 256 (accept_3_3 62 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 256 (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 256 (accept_3_3 59 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 256 (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 87
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 256 (accept_3_3 56 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 256 (accept_3_3 53 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 51 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 256 (accept_3_3 50 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 256 (accept_3_3 47 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 256
  (Polychromatic418967fa.accept_18_9_15_4_1_5173 45 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 256 (accept_3_3 44 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 256 (accept_3_3 41 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 256 (accept_3_3 38 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 256 (accept_3_3 35 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 256 (accept_3_3 32 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 256 (accept_3_3 29 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 256 (accept_3_3 26 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 256 (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 256 (accept_3_3 23 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 256 (accept_3_3 20 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 256 (accept_3_3 17 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 256 (accept_3_3 14 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 256 (accept_3_3 11 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 256
  (Polychromatic418967fa.accept_18_9_15_4_1_5173 9 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 256 (accept_3_3 8 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 256 (accept_3_3 5 87 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 87 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 256 (accept_3_3 2 87 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 256
  (allA_of_3_1 86 86 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 256 (allA_succ_of_accept 84 85 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 84 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 256 (accept_3_3 83 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 256 (accept_3_3 80 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 79 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 256
  (Polychromatic418967fa.accept_20_18_5_16_1_5425 78 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 256 (accept_3_3 77 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 256 (Polychromatic418967fa.accept_13_11_7_9_1_612 76 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 256 (accept_3_3 74 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 256
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 256 (accept_3_3 71 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 256 (accept_3_3 68 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 256 (Polychromatic418967fa.accept_13_2_7_9_1_2616 67 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 256 (accept_3_3 65 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 256 (accept_3_3 62 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 256 (accept_3_3 59 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 256 (accept_3_3 56 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 256 (Polychromatic418967fa.accept_13_3_7_9_1_1153 55 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 256 (accept_3_3 53 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 256 (accept_3_3 50 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 256
  (Polychromatic418967fa.accept_27_21_4_13_1_15624 48 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 85 256 (accept_3_3 47 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 85 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 85 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 256 (accept_3_3 44 85 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260
  43 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 256
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 256 (accept_3_3 41 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 256 (accept_3_3 38 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 256 (Polychromatic418967fa.accept_13_11_7_9_1_612 37 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 256 (accept_3_3 35 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 256 (accept_3_3 32 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 256
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 256 (accept_3_3 29 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 256 (accept_3_3 26 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 25 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 256 (accept_3_3 23 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 256 (accept_3_3 20 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 256
  (Polychromatic418967fa.accept_20_18_5_16_1_5425 18 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 256 (accept_3_3 17 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 256 (accept_3_3 14 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 256 (accept_3_3 11 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 256 (accept_3_3 8 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 256 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 256
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 256 (accept_3_3 5 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 256 (accept_3_3 2 85 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 85 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 256
  (allA_succ_of_accept 83 84 256 (accept_3_3 83 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  256 2 41 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 256 4 20 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 256 2 39 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 256 (accept_3_3 77 84 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 256 4 19 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 256 2 37 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 256 4 18 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 256 (accept_3_3 71 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 256 2 35 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 256 4 17 21 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 256
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 256 2 33 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 256 (accept_3_3 65 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 256 4 16 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 256 (Polychromatic418967fa.accept_17_12_16_1_1_8363 63 84 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 256 2 31 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 256 4 15 21 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 256 (accept_3_3 59
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 256 2 29 42 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 256
  (Polychromatic418967fa.accept_22_13_18_14_1_13974 57 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 84 256 4 14 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 84 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 256 2 27 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 256 (accept_3_3 53 84 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 256 4 13 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 256 2 25 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 84 256 (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 84 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 256 4 12 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 256 (accept_3_3 47 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 256 2 23 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 256 4 11 21 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 256 2 21 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 256 (accept_3_3 41 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 256 4 10 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 256 (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 84 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 256 2 19 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 37
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 256 4 9 21 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 256 (accept_3_3 35
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 256 2 17 42 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 256 4 8 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 256 (Polychromatic418967fa.accept_24_7_12_16_1_12190 31 84 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 256 2 15 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 256 (accept_3_3 29 84 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 256 4 7 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 84 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 256 2 13 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 256 4 6 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 256 (accept_3_3 23 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  256 2 11 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 84 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 256 4 5 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 256 2 9 42 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 256 (accept_3_3 17 84 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 256 4 4 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 256 2 7 42 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 256
  (Polychromatic418967fa.accept_22_13_18_14_1_13974 13 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 84 256 4 3 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 84 256 (accept_3_3 11 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 256 2 5 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 84 256 (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 84 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 256 4 2 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 256 2 3 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 256 (accept_3_3 5 84 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 256 4 1 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3
  84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 256 2 1 42 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 256
  (allA_of_3_1 83 83 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 256 (allA_succ_of_accept 81 82 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 256 2 40 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 256 2 39 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 256 (accept_3_3 77 82 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 256 2 38 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 75
  82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 256 2 37 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 256 2 36 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 256 (accept_3_3 71 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 256 2 35 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 256 2 34 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 256 2 33 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 256 (accept_3_3 65 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 256 2 32 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 256 2 31 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 256 2 30 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 256 (accept_3_3 59 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 256 2 29 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 256 2 28 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 256 2 27 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 256 (accept_3_3 53 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 256 2 26 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 256 2 25 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 256 2 24 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 256 (accept_3_3 47 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 256 2 23 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 256 2 22 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 256 2 21 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 256 (accept_3_3 41 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 256 2 20 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 256 2 19 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 256 2 18 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 256 (accept_3_3 35 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 256 2 17 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 256 2 16 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 256 2 15 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 256 (accept_3_3 29 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 256 2 14 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 256 2 13 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 256 2 12 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 256 (accept_3_3 23 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 256 2 11 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 256 2 10 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 256 2 9 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 256 (accept_3_3 17 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  256 2 8 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 256 2 7 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 256 2 6 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 256 (accept_3_3 11 82 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 256 2 5 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 256 2 4 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 256 2 3 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 256 (accept_3_3 5 82 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 256 2 2 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 256 2 1 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 256
  (allA_succ_of_accept 80 81 256 (accept_3_3 80 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 78 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 256 (accept_3_3 77 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 256 (Polychromatic418967fa.accept_21_13_18_4_1_11181 76 81 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 256
  (Polychromatic418967fa.accept_10_5_1_6_1_672 75 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 256 (accept_3_3 74 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 256 (accept_3_3 71 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 256 (Polychromatic418967fa.accept_13_5_3_9_1_1189 70 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 69 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 256 (accept_3_3 68 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 256 (accept_3_3 65 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 256 (Polychromatic418967fa.accept_13_12_3_9_1_4341 64 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 256
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 63 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 256 (accept_3_3 62 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 256 (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 256 (accept_3_3 59 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 256 (Polychromatic418967fa.accept_13_6_3_9_1_1827 58 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 256
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 256 (accept_3_3 56 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 256 (accept_3_3 53 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 51 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 256 (accept_3_3 50 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 256 (accept_3_3 47 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 46 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 256
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 256 (accept_3_3 44 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 256 (accept_3_3 41 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 256 (accept_3_3 38 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 256 (accept_3_3 35 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 256 (Polychromatic418967fa.accept_13_8_3_9_1_5269 34 81 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 256
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 256 (accept_3_3 32 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 256 (accept_3_3 29 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 256
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 256 (accept_3_3 26 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 256 (accept_3_3 23 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 256
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 256 (accept_3_3 20 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 256 (accept_3_3 17 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 256 (Polychromatic418967fa.accept_28_16_25_4_1_15623 16 81 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 256
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 256 (accept_3_3 14 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 256 (accept_3_3 11 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 256 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 81 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 256 (accept_3_3 8 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 256 (accept_3_3 5 81 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 256 (Polychromatic418967fa.accept_19_4_5_9_1_8855 4 81 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3
  81 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 256 (accept_3_3 2 81 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 256 (allA_of_3_1 80
  80 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 256 (allA_succ_of_accept 78 79 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 256 (accept_3_3 77 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 256 (accept_3_3 74 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 256
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 256 (accept_3_3 71 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 256 (accept_3_3 68 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 67 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 256 (accept_3_3 65 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 256 (accept_3_3 62 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 256 (accept_3_3 59 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 256 (accept_3_3 56 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 256 (accept_3_3 53 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 52 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 256 (accept_3_3 50 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 256 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 256 (accept_3_3 47 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 256 (accept_3_3 44 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 256 (accept_3_3 41 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 256 (accept_3_3 38 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 256
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 256 (accept_3_3 35 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 256 (accept_3_3 32 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 256 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 256 (accept_3_3 29 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 256 (accept_3_3 26 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 256 (accept_3_3 23 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 256 (accept_3_3 20 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 256
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 256 (accept_3_3 17 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 256 (accept_3_3 14 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 256 (accept_3_3 11 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 256 (accept_3_3 8 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 256 (Polychromatic418967fa.accept_17_7_11_1_1_4503 7 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 256 (accept_3_3 5 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  256 (Polychromatic418967fa.accept_22_4_13_14_1_15622 4 79 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 256 (accept_3_3 2 79 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 256
  (allA_succ_of_accept 77 78 256 (accept_3_3 77 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  256 2 38 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 256 2 37 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 78 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 256 2 36 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 256 (accept_3_3 71 78 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 256 2 35 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 256 2 34 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 256 (Polychromatic418967fa.accept_14_11_8_4_1_2628 67 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 256 2 33 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 256 (accept_3_3 65 78 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 256 2 32 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63
  78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 256 2 31 39 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 256 2 30 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 256 (accept_3_3 59 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 256 2 29 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 78 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 256 2 28 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 256 2 27 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 256 (accept_3_3 53 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 256 2 26 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 78 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 256 2 25 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 256
  (Polychromatic418967fa.accept_15_4_3_1_1_487 49 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 256 2 24 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 256 (accept_3_3 47 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 256 2 23 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 256 2 22 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 256 2 21 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 256 (accept_3_3 41 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 256 2 20 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 78 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 256 2 19 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 256 2 18 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 256 (accept_3_3 35 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 256 2 17 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 256 2 16 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 256 2 15 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 256 (accept_3_3 29 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 256 2 14 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 256 2 13 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 256 2 12 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 256 (accept_3_3 23 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 256 2 11 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 256 2 10 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 256 2 9 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 256 (accept_3_3 17 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  256 2 8 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 256 2 7 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 78 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 78 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 256 2 6 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 256 (accept_3_3 11 78 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 256 2 5 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 256 2 4 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 256 2 3 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 256 (accept_3_3 5 78 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 256 2 2 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 256 2 1 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 256 (allA_of_3_1 77 77
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 256 (allA_succ_of_accept 75 76 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 256 2 37 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 76 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 256 4 18 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 256 (accept_3_3 71 76 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 256 2 35 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 256 (Polychromatic418967fa.accept_21_6_13_4_1_6521
  69 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 256 4 17 19 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 67 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 256 2 33 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 256 (accept_3_3 65 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 256 4 16 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 76 256 (Polychromatic418967fa.accept_24_15_4_16_1_8786 63 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 256 2 31 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 61
  76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 256 4 15 19 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 256 (accept_3_3 59
  76 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 256 2 29 38 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 256
  (Polychromatic418967fa.accept_24_9_4_16_1_12173 57 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 256 4 14 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 256 (Polychromatic418967fa.accept_17_4_8_1_1_5740 55 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 256 2 27 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 256 (accept_3_3 53 76 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 256 4 13 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 256 2 25 38 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 256
  (Polychromatic418967fa.accept_21_7_13_4_1_2169 49 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 256 4 12 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 256 (accept_3_3 47 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  256 2 23 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 76 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 256 4 11 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 256 (Polychromatic418967fa.accept_17_9_8_1_1_7036 43 76 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 256 2 21 38 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 256 (accept_3_3 41 76 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 256 4 10 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 256
  (Polychromatic418967fa.accept_21_18_13_4_1_14089 39 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 76 256 2 19 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 76 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 256 4 9 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 256 (accept_3_3 35 76 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 256 2 17 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 256 4 8 19 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 256 2 15 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 256 (accept_3_3 29 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 256 4 7 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 76 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 256 2 13 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 256
  (Polychromatic418967fa.accept_27_25_22_13_1_15621 25 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 76 256 4 6 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 256 (accept_3_3 23 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 76 256 2 11 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 76 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 256 4 5 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 256 2 9 38 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 256 (accept_3_3 17
  76 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 256 4 4 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 15 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 76 256 2 7 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 76 256 (Polychromatic418967fa.accept_25_13_1_6_1_13770 13 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 256 4 3 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 256 (accept_3_3 11 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 76 256 2 5 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 76 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 256 4 2 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 256
  (Polychromatic418967fa.accept_11_7_10_3_1_633 7 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 256 2 3 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 256 (accept_3_3 5 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 256
  4 1 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 256 2 1 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 76 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 256 (allA_succ_of_accept
  74 75 256 (accept_3_3 74 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 256 (accept_3_3 71 75 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69
  75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 256 (accept_3_3 68 75
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 256 (accept_3_3 65 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 256 (Polychromatic418967fa.accept_19_6_18_9_1_10323 63 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 256 (accept_3_3 62 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 75 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 256 (accept_3_3 59 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 256 (accept_3_3 56 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 256 (accept_3_3 53 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 256 (accept_3_3 50 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 256 (accept_3_3 47 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 256 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 256 (accept_3_3 44 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 256 (accept_3_3 41 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 256 (Polychromatic418967fa.accept_13_1_10_9_1_215 40 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 256 (accept_3_3 38 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 256 (accept_3_3 35 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 256 (accept_3_3 32 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 256 (accept_3_3 29 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 256 (accept_3_3 26 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 256 (accept_3_3 23 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 256 (accept_3_3 20 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 256 (accept_3_3 17 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 256 (accept_3_3 14 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 256
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 256 (accept_3_3 11 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 256 (accept_3_3 8 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 256 (accept_3_3 5 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 75 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 256 (Polychromatic418967fa.accept_19_3_18_9_1_4580 3 75 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 256 (accept_3_3 2 75 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 256 (allA_of_3_1 74 74
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 256 (allA_succ_of_accept 72 73 256
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 256 (accept_3_3 71 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 256 (accept_3_3 68 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 67 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 256 (accept_3_3 65 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 256 (accept_3_3 62 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 256 (accept_3_3 59 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 256 (accept_3_3 56 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 256
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 256 (accept_3_3 53 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 256 (accept_3_3 50 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 256 (accept_3_3 47 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 256 (accept_3_3 44 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 256 (accept_3_3 41 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 256 (accept_3_3 38 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 256 (accept_3_3 35 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 256 (accept_3_3 32 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 256 (Polychromatic418967fa.accept_19_12_16_9_1_5976 31 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 256 (accept_3_3 29 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 256 (accept_3_3 26 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 256 (accept_3_3 23 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 256 (accept_3_3 20 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 256 (accept_3_3 17 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 256 (accept_3_3 14 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 256 (accept_3_3 11 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 256 (accept_3_3 8 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 256 (accept_3_3 5 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 73 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 256 (accept_3_3 2 73 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 256 (allA_succ_of_accept 71
  72 256 (accept_3_3 71 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 256 2 35 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 256 4 17 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 256 (Polychromatic418967fa.accept_13_2_7_9_1_2616 67 72 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 256 2 33 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 256 (accept_3_3 65 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 256 8 8 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 72 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 256 2 31 36 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 256 4 15 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 256 (accept_3_3 59 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  256 2 29 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 72 256 (Polychromatic418967fa.accept_21_15_9_4_1_2207 57 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 256 8 7 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 256 2 27 36 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 256 (accept_3_3 53 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 256 4 13 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 51
  72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 256 2 25 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 256
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 256 8 6 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 256 (accept_3_3 47 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72
  256 2 23 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 72 256 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 72 256 4 11 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 72 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 43 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 256 2 21 36 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 256 (accept_3_3 41 72 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 256 8 5 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 256 (Polychromatic418967fa.accept_17_5_4_1_1_3369
  39 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 256 2 19 36 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 256
  (Polychromatic418967fa.accept_13_11_7_9_1_612 37 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 256 4 9 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 256 (accept_3_3 35 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  256 2 17 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 72 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 256 8 4 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 256 2 15 36 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 256 (accept_3_3 29 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 256 4 7 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 256 2 13 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 256
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 25 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 256 8 3 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 256 (accept_3_3 23 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  256 2 11 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 72 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 256 4 5 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 256 2 9 36 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 256 (accept_3_3 17 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 256 8 2 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 256 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 72 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 256 2 7 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 256 4 3 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 256 (accept_3_3 11 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  256 2 5 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 256 8 1 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 256 (Polychromatic418967fa.accept_25_7_22_6_1_13813 7 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 256 2 3 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 256 (accept_3_3 5 72 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 256 4 1 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 256 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 72 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 256 2 1 36 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 72 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 256
  (allA_of_3_1 71 71 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 256 (allA_succ_of_accept 69 70 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 256 2 34 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 256 2 33 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 256 (accept_3_3 65 70 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 256 2 32 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 256 (Polychromatic418967fa.accept_19_6_13_9_1_3291
  63 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 256 2 31 35 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 256 2 30 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 70 256 (accept_3_3 59 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 70 256 2 29 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 70 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 256 2 28 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 256 2 27 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 256 (accept_3_3 53 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 256 2 26 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 256 2 25 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 256 2 24 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 70 256 (accept_3_3 47 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 70 256 2 23 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 70 256 (Polychromatic418967fa.accept_19_7_13_9_1_10179 45 70 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 256 2 22 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 256 2 21 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 256 (accept_3_3 41 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 256 2 20 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 256 2 19 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 256 2 18 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 70 256 (accept_3_3 35 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 256 2 17 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 256 2 16 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 256 2 15 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 256 (accept_3_3 29 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 256 2 14 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 70 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 256 2 13 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 256 2 12 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 70 256 (accept_3_3 23 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 256 2 11 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 70 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 256 2 10 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 256 2 9 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 256 (accept_3_3 17 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  256 2 8 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 256 2 7 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 70 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 70 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 256 2 6 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 256 (accept_3_3 11 70 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 256 2 5 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 256
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 70 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 256 2 4 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 70 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 256 2 3 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 256 (accept_3_3 5 70 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 256 2 2 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 256 2 1 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 256 (allA_succ_of_accept 68 69
  256 (accept_3_3 68 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 256 (accept_3_3 65 69 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 63
  69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 256 (accept_3_3 62 69
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 256
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 69 256 (accept_3_3 59 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  69 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 256 (accept_3_3 56 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 256 (accept_3_3 53 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 256 (accept_3_3 50 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 256 (accept_3_3 47 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 256 (accept_3_3 44 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 256 (accept_3_3 41 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 256 (accept_3_3 38 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 256 (accept_3_3 35 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 256 (accept_3_3 32 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 256 (accept_3_3 29 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 256 (Polychromatic418967fa.accept_18_9_15_4_1_5173 27 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 256 (accept_3_3 26 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 256 (accept_3_3 23 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 256 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 256 (accept_3_3 20 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 256 (accept_3_3 17 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 256 (accept_3_3 14 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 256 (accept_3_3 11 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 256 (accept_3_3 8 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 256 (accept_3_3 5 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  256 (Polychromatic418967fa.accept_22_4_3_14_1_15620 4 69 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 256 (accept_3_3 2 69 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 256 (allA_of_3_1 68 68 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 256 (allA_succ_of_accept 66 67 256
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 66 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 256 (accept_3_3 65 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 64 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 256 (accept_3_3 62 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 256
  (Polychromatic418967fa.accept_19_3_10_9_1_7338 60 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 256 (accept_3_3 59 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 256 (accept_3_3 56 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 55 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 256
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 256 (accept_3_3 53 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 256 (Polychromatic418967fa.accept_22_8_1_14_1_7786 52 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 256 (accept_3_3 50 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 49 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 256
  (Polychromatic418967fa.accept_25_23_17_6_1_15619 48 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 67 256 (accept_3_3 47 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 67 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 46 67 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 256 (accept_3_3 44 67 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 256 (Polychromatic418967fa.accept_10_3_7_6_1_659
  43 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 256
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 256 (accept_3_3 41 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 256 (accept_3_3 38 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 256 (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 256
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 256 (accept_3_3 35 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 256 (accept_3_3 32 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 256
  (Polychromatic418967fa.accept_22_8_1_14_1_7786 30 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 256 (accept_3_3 29 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 256 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 256 (accept_3_3 26 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 256 (accept_3_3 23 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 256 (accept_3_3 20 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 256 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 256
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 256 (accept_3_3 17 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 256 (accept_3_3 14 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 256
  (Polychromatic418967fa.accept_17_12_16_1_1_8363 12 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 256 (accept_3_3 11 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 256 (accept_3_3 8 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 256 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 256
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 256 (accept_3_3 5 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  256 (Polychromatic418967fa.accept_19_4_10_9_1_4569 4 67 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 256 (accept_3_3 2 67 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 67 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 256 (allA_succ_of_accept 65 66
  256 (accept_3_3 65 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 256 2 32 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 256
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 256 2 31 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 256 2 30 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 256 (accept_3_3 59 66 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 256 2 29 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57
  66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 256 2 28 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 256 2 27 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 256 (accept_3_3 53 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 256 2 26 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 66 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 256 2 25 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 256
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 256 2 24 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 256 (accept_3_3 47 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 256 2 23 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 66 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 256 2 22 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 256 2 21 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 256 (accept_3_3 41 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 256 2 20 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 66 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 256 2 19 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 256 2 18 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 256 (accept_3_3 35 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 256 2 17 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 66 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 256 2 16 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 256
  (Polychromatic418967fa.accept_13_5_1_9_1_618 31 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 256 2 15 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 256 (accept_3_3 29 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 256 2 14 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 256 2 13 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 256 2 12 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 256 (accept_3_3 23 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 256 2 11 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 66 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 256 2 10 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 256 2 9 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 256 (accept_3_3 17 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  256 2 8 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 256 2 7 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 66 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 256 2 6 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 256 (accept_3_3 11 66 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 256 2 5 33 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 256 2 4 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 256 2 3 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 256 (accept_3_3 5 66 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 256 2 2 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 256 2 1 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 256 (allA_of_3_1 65 65 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 256 (allA_succ_of_accept 63 64 256
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 256 2 31 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 64 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 256 4 15 16 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 256 (accept_3_3 59 64 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 256 2 29 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57
  64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 256 8 7 8 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 256 2 27 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 256 (accept_3_3 53 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 64 256 4 13 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 64 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 64 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 256 2 25 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 256 (Polychromatic418967fa.accept_13_10_12_9_1_1837
  49 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 256 16 3 4 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 256 (accept_3_3 47
  64 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 256 2 23 32 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 256 4 11 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 256 2 21 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 256 (accept_3_3 41 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 256 8 5 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 64 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 64 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 256 2 19 32 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 256
  (Polychromatic418967fa.accept_28_9_8_4_1_15618 37 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 256 4 9 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 256 (accept_3_3 35 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  256 2 17 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 64 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 256 32 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 256 2 15 32 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 256 (accept_3_3 29 64 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 256 4 7 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 256 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 64 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 256 2 13 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 256 8 3 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 256 (accept_3_3 23 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  256 2 11 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 64 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 256 4 5 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 256 2 9 32 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 256 (accept_3_3 17 64 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 256 16 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 256 2 7 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 256
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 256 4 3 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 256 (accept_3_3 11 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  256 2 5 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 256 (Polychromatic418967fa.accept_22_9_20_14_1_9412 9 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 256 8 1 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 256 2 3 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 256 (accept_3_3 5 64 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 256 4 1 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 256 2 1 32 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 256
  (Polychromatic418967fa.accept_22_1_20_14_1_11000 1 64 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 256
  (allA_succ_of_accept 62 63 256 (accept_3_3 62 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 256 (accept_3_3 59 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 256
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 256 (accept_3_3 56 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 256 (accept_3_3 53 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 256
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 256 (accept_3_3 50 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 256 (accept_3_3 47 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 256 (Polychromatic418967fa.accept_13_7_11_9_1_1858 46 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 256
  (Polychromatic418967fa.accept_14_3_7_4_1_118 45 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 256 (accept_3_3 44 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 256 (accept_3_3 41 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 256
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 256 (accept_3_3 38 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 256 (accept_3_3 35 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 256
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 256 (accept_3_3 32 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 256 (accept_3_3 29 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 256
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 256 (accept_3_3 26 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 256 (accept_3_3 23 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 256 (Polychromatic418967fa.accept_19_3_6_9_1_7334 22 63 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 256
  (Polychromatic418967fa.accept_13_8_11_9_1_593 21 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 256 (accept_3_3 20 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 256 (accept_3_3 17 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 15 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 256 (accept_3_3 14 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 256 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 256 (accept_3_3 11 63 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 63
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 256
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 256 (accept_3_3 8 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 63 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 256 (accept_3_3 5 63 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 256 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 63 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 256 (Polychromatic418967fa.accept_14_3_7_4_1_118 3
  63 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 256 (accept_3_3 2 63 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 256 (allA_of_3_1 62 62 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 256 (allA_succ_of_accept 60 61 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 256 (accept_3_3 59 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 256 (accept_3_3 56 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 256
  (Polychromatic418967fa.accept_19_16_4_9_1_10196 54 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 256 (accept_3_3 53 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 256 (accept_3_3 50 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 256 (accept_3_3 47 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 256 (accept_3_3 44 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 256 (accept_3_3 41 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 256 (Polychromatic418967fa.accept_19_2_4_9_1_1131 40 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 256 (accept_3_3 38 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 256 (accept_3_3 35 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 256 (accept_3_3 32 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 256 (accept_3_3 29 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 256 (accept_3_3 26 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 256 (accept_3_3 23 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 256 (accept_3_3 20 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 256
  (Polychromatic418967fa.accept_20_18_1_16_1_15617 18 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 256 (accept_3_3 17 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 256 (accept_3_3 14 61 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 256 (accept_3_3 11 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 256 (accept_3_3 8 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 256 (accept_3_3 5 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  256 (Polychromatic418967fa.accept_23_4_15_3_1_15616 4 61 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 256 (accept_3_3 2 61 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 256 (allA_succ_of_accept 59 60 256
  (accept_3_3 59 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 256 2 29 30 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 256 4 14 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 60 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 256 2 27 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 256 (accept_3_3 53 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 256 4 13 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 256 (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 60 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 256 2 25 30 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 256
  (Polychromatic418967fa.accept_17_15_9_1_1_3363 49 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 256 4 12 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 256 (accept_3_3 47 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60
  256 2 23 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 60 256 (Polychromatic418967fa.accept_21_3_18_4_1_11234 45 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 256 4 11 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 256 2 21 30 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 256 (accept_3_3 41 60 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 256 4 10 15 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 256 2 19 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 256 4 9 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 256 (accept_3_3 35 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 256 2 17 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 60 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 256 4 8 15 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 256
  (Polychromatic418967fa.accept_19_12_3_9_1_10338 31 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 256 2 15 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 256 (accept_3_3 29 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 256 4 7 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 60 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 60 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 256 2 13 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 25
  60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 256 4 6 15 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 256 (accept_3_3 23
  60 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 256 2 11 30 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 256 4 5 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 256 2 9 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 256 (accept_3_3 17 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 256 4 4 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 60 256 (Polychromatic418967fa.accept_17_15_9_1_1_3363 15 60 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 256 2 7 30 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 256
  (Polychromatic418967fa.accept_19_13_3_9_1_5980 13 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 256 4 3 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 256 (accept_3_3 11 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  256 2 5 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 256 (Polychromatic418967fa.accept_21_9_18_4_1_4953 9 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 256 4 2 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 256 2 3 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 256 (accept_3_3 5 60 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 256 4 1 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 256 2 1 30 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 256 (allA_of_3_1 59 59 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 256 (allA_succ_of_accept 57 58 256
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 256 2 28 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 256 2 27 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 256 (accept_3_3 53 58 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 256 2 26 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814
  51 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 256 2 25 29 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 256 2 24 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 256 (accept_3_3 47 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 256 2 23 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 256 (Polychromatic418967fa.accept_17_11_7_1_1_7023 45 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 256 2 22 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 256 2 21 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 256 (accept_3_3 41 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 256 2 20 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 256 (Polychromatic418967fa.accept_24_15_10_16_1_10574 39 58 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 256 2 19 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 256 2 18 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 256 (accept_3_3 35 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 256 2 17 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 256 2 16 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 256 2 15 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 256 (accept_3_3 29 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 256 2 14 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 256 2 13 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 256 2 12 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 256 (accept_3_3 23 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 256 2 11 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 256 (Polychromatic418967fa.accept_19_2_1_9_1_10240 21 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 256 2 10 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 256 2 9 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 256 (accept_3_3 17 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  256 2 8 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 256 2 7 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 256 2 6 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 256 (accept_3_3 11 58 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 256 2 5 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 256
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 256 2 4 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 256 2 3 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 256 (accept_3_3 5 58 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 256 2 2 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 58 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 256 2 1 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  58 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 256 (allA_succ_of_accept 56 57 256
  (accept_3_3 56 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 256 (accept_3_3 53 57 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 256 (accept_3_3 50 57
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 256
  (Polychromatic418967fa.accept_21_6_15_4_1_5021 48 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 256 (accept_3_3 47 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 256 (accept_3_3 44 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 256 (accept_3_3 41 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 256 (accept_3_3 38 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 256
  (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 256 (accept_3_3 35 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 256 (accept_3_3 32 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 256 (accept_3_3 29 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 256 (accept_3_3 26 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 256 (accept_3_3 23 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 256 (Polychromatic418967fa.accept_17_5_6_1_1_5735 22 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 256 (accept_3_3 20 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 256 (accept_3_3 17 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 256 (accept_3_3 14 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 256 (accept_3_3 11 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 256 (Polychromatic418967fa.accept_21_9_15_4_1_2190 9 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 256 (accept_3_3 8 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 256 (accept_3_3 5 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 57 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 256 (accept_3_3 2 57 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 256 (allA_of_3_1 56 56 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 256 (allA_succ_of_accept 54 55 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 256 (accept_3_3 53 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 256 (accept_3_3 50 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 256 (accept_3_3 47 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 256 (accept_3_3 44 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 256 (accept_3_3 41 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 256 (accept_3_3 38 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 256 (accept_3_3 35 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 256 (accept_3_3 32 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 256 (accept_3_3 29 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 256 (accept_3_3 26 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 256 (accept_3_3 23 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 256 (accept_3_3 20 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 256
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 256 (accept_3_3 17 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 256 (accept_3_3 14 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 256 (accept_3_3 11 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 256 (accept_3_3 8 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 256 (accept_3_3 5 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 55 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 256 (accept_3_3 2 55 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 55 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 256 (allA_succ_of_accept 53 54 256 (accept_3_3 53 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 256 2 26 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 256 2 25 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 256
  (Polychromatic418967fa.accept_17_15_3_1_1_9696 49 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 256 2 24 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 54 256 (accept_3_3 47 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 256 2 23 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 256 2 22 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 256 2 21 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 256 (accept_3_3 41 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 256 2 20 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 54 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 256 2 19 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 256 2 18 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 256 (accept_3_3 35 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 256 2 17 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 256 2 16 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 256
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 256 2 15 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 256 (accept_3_3 29 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 256 2 14 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 256 2 13 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 256 2 12 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 256 (accept_3_3 23 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 256 2 11 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 256 2 10 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 256
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 256 2 9 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 256 (accept_3_3 17 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  256 2 8 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 256 2 7 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 256 2 6 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 256 (accept_3_3 11 54 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 256 2 5 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 256 2 4 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 54 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 256 2 3 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 256 (accept_3_3 5 54 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 256 2 2 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 256 2 1 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 256 (allA_of_3_1 53 53 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 256 (allA_succ_of_accept 51 52 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51
  52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 256 2 25 26 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 256 4 12 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 256 (accept_3_3 47 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  256 2 23 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 52 256 (Polychromatic418967fa.accept_22_1_8_14_1_14026 45 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 256 4 11 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 256 2 21 26 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 256 (accept_3_3 41 52 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 256 4 10 13 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 256 2 19 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 52 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 256 4 9 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 256 (accept_3_3 35 52 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 256 2 17 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 52 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 256 4 8 13 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 256 2 15 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 256 (accept_3_3 29 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 256 4 7 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 52 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 256 2 13 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686
  25 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 256 4 6 13 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 256 (accept_3_3 23
  52 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 256 2 11 26 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 256 4 5 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 256 2 9 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 256 (accept_3_3 17 52 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 256 4 4 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 256 2 7 26 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 256 4 3 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 256 (accept_3_3 11 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  256 2 5 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 256 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 256 4 2 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 256 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 52 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 256 2 3 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 256 (accept_3_3 5 52 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 256 4 1 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 256 2 1 26 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 256)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 256 (allA_succ_of_accept 50 51 256
  (accept_3_3 50 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 256 (accept_3_3 47 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 256 (Polychromatic418967fa.accept_10_5_1_6_1_672
  45 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 256 (accept_3_3 44
  51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 256 (accept_3_3 41 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 256 (accept_3_3 38 51
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 256
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 256 (accept_3_3 35 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 256 (accept_3_3 32 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 256 (accept_3_3 29 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 256 (accept_3_3 26 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 256 (accept_3_3 23 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 256 (accept_3_3 20 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 256 (accept_3_3 17 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 256 (accept_3_3 14 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 256 (accept_3_3 11 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 256 (accept_3_3 8 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 256 (accept_3_3 5 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 51 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 256 (accept_3_3 2 51 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 256)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 256 (allA_of_3_1 50 50 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 256
  (allA_succ_of_accept 48 49 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 256 (accept_3_3 47 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 256 (accept_3_3 44 49
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 43 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 256 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 256 (accept_3_3 41 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 256 (Polychromatic418967fa.accept_13_1_10_9_1_215 40 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 256 (accept_3_3 38 49
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 256
  (Polychromatic418967fa.accept_17_3_15_1_1_3348 37 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 49 256 (Polychromatic418967fa.accept_19_17_11_9_1_2141 36 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 256 (accept_3_3 35 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 49 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33
  49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 256 (accept_3_3 32 49
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 256
  (Polychromatic418967fa.accept_14_3_7_4_1_118 31 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 49 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 256 (accept_3_3 29 49 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 49 256 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 256 (accept_3_3 26 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 256 (accept_3_3 23 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 256 (accept_3_3 20 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 256 (accept_3_3 17 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 256 (Polychromatic418967fa.accept_17_16_15_1_1_11968 16 49 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 256 (accept_3_3 14 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 256 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 256 (accept_3_3 11 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 256 (accept_3_3 8 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 256 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 256 (accept_3_3 5 49 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 256 (Polychromatic418967fa.accept_27_4_22_13_1_15615 4 49 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 256 (accept_3_3 2 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  256 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 49 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 256))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 256 (allA_succ_of_accept
  47 48 256 (accept_3_3 47 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 256 2 23 24 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 256 4 11 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 48 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 256 2 21 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 256 (accept_3_3 41 48 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 256 8 5 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 256 (Polychromatic418967fa.accept_19_1_10_9_1_10302 39 48 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 256 2 19 24 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 256 4 9 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 256 (accept_3_3 35 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  256 2 17 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 48 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 256 16 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 256 2 15 24 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 256 (accept_3_3 29 48 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 256 4 7 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 256 (Polychromatic418967fa.accept_17_10_14_1_1_5823 27 48
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 256 2 13 24 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 256 8 3 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 256 (accept_3_3 23 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  256 2 11 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 48 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 256 4 5 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 256 2 9 24 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 256 (accept_3_3 17 48 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 256 16 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 256 2 7 24 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 256 4 3 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 256 (accept_3_3 11 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  256 2 5 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 256 8 1 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 256 2 3 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 256 (accept_3_3 5 48 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 256 4 1 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 256 2 1 24 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 256)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 256 (allA_of_3_1 47 47 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 256 (allA_succ_of_accept 45 46 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 256 2 22 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 46 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 256 2 21 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 256 (accept_3_3 41 46 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 256 2 20 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39
  46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 256 2 19 23 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 256 2 18 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 256 (accept_3_3 35 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 256 2 17 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 256 2 16 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 256 2 15 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 256 (accept_3_3 29 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 256 2 14 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 256 (Polychromatic418967fa.accept_20_7_6_16_1_11369 27 46 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 256 2 13 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 256 2 12 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 256 (accept_3_3 23 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 256 2 11 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 256 2 10 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 256 2 9 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 256 (accept_3_3 17 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  256 2 8 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 256 2 7 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 46 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 256 2 6 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 256 (accept_3_3 11 46 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 256 2 5 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 256
  (Polychromatic418967fa.accept_24_9_22_16_1_826 9 46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 256 2 4 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 256 2 3 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 256 (accept_3_3 5 46 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 256 2 2 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 256 2 1 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 1
  46 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  256)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 256 (allA_succ_of_accept 44 45 256 (accept_3_3 44 45
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 256 (accept_3_3 41 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 256 (accept_3_3 38 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 256 (accept_3_3 35 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 256 (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 256 (accept_3_3 32 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 256 (accept_3_3 29 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 256 (accept_3_3 26 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 256 (accept_3_3 23 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 256 (accept_3_3 20 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 256 (accept_3_3 17 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 256 (accept_3_3 14 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 256
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 256 (accept_3_3 11 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 256 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 256 (accept_3_3 8 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 256 (accept_3_3 5 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 45 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 256 (accept_3_3 2 45 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 256))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  256 (allA_of_3_1 44 44 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 256 (allA_succ_of_accept 42 43 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 256 (accept_3_3 41 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 256 (accept_3_3 38 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 256
  (Polychromatic418967fa.accept_24_12_19_16_1_15614 36 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 43 256 (accept_3_3 35 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 43 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 256 (accept_3_3 32 43 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 256 (accept_3_3 29 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 256 (accept_3_3 26 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 25 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 256 (accept_3_3 23 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 256 (accept_3_3 20 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 256 (accept_3_3 17 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 256 (accept_3_3 14 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 256 (accept_3_3 11 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 256 (accept_3_3 8 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 256 (accept_3_3 5 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  256 (Polychromatic418967fa.accept_19_4_5_9_1_8855 4 43 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 256 (accept_3_3 2 43 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 256)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 256 (allA_succ_of_accept 41 42 256 (accept_3_3 41 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 256 2 20 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 256 2 19 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 256 2 18 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 42 256 (accept_3_3 35 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 256 2 17 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 42 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 256 2 16 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 256 2 15 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 256 (accept_3_3 29 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 256 2 14 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 42 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 256 2 13 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 256 2 12 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 256 (accept_3_3 23 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 256 2 11 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 42 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 256 2 10 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 256 2 9 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 256 (accept_3_3 17 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  256 2 8 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 256 2 7 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 42 256 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 42 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 256 2 6 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 256 (accept_3_3 11 42 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 256 2 5 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 256 2 4 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 256 2 3 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 256 (accept_3_3 5 42 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 256 2 2 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 256 2 1 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  256)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 256 (allA_of_3_1 41 41 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 256 (allA_succ_of_accept 39 40 256 (Polychromatic418967fa.accept_15_9_10_1_1_1062 39 40 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 256 2 19 20 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 256 4 9 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 256 (accept_3_3 35 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40
  256 2 17 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 40 256 (Polychromatic418967fa.accept_21_12_19_4_1_15613 33 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 40 256 8 4 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 256 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 40 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 256 2 15 20 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 256 (accept_3_3 29 40 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 256 4 7 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 256 2 13 20 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 256
  (Polychromatic418967fa.accept_28_25_12_4_1_15612 25 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 40 256 8 3 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 40 256 (accept_3_3 23 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 256 2 11 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 40 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 256 4 5 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 256 (Polychromatic418967fa.accept_13_6_1_9_1_619 19
  40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 256 2 9 20 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 256 (accept_3_3 17
  40 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 256 8 2 5 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 40 256 2 7 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 40 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 256 4 3 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 256 (accept_3_3 11 40 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 40 256 2 5 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 40 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 256 8 1 5 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 256
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 256 2 3 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 40 256 (accept_3_3 5 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 256
  4 1 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40
  256 (Polychromatic418967fa.accept_17_3_6_1_1_8382 3 40 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 40 256 2 1 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 40 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 256)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 256
  (allA_succ_of_accept 38 39 256 (accept_3_3 38 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 256 (accept_3_3 35 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 39 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 256 (accept_3_3 32 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 256 (accept_3_3 29 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 256
  (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 256 (accept_3_3 26 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 256 (accept_3_3 23 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 256
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 256 (accept_3_3 20 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 256 (accept_3_3 17 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 256 (accept_3_3 14 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 256 (Polychromatic418967fa.accept_19_12_1_9_1_10281 12 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 256 (accept_3_3 11 39 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 39 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 256 (accept_3_3 8 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 256 (accept_3_3 5 39 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 256 (Polychromatic418967fa.accept_17_4_5_1_1_5776 4 39 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  39 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 256 (accept_3_3 2 39 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  256))))))))))))))))))))))))))))))))))))))) (allB_succ 38 256 (allA_of_3_1 38 38 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 256 (allA_succ_of_accept 36 37 256 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 37 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 256 (accept_3_3 35 37 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34
  37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 256 (accept_3_3 32 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 256 (accept_3_3 29 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 256 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 37 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 256 (accept_3_3 26 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 256 (accept_3_3 23 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 256 (accept_3_3 20 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 256 (accept_3_3 17 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 256 (accept_3_3 14 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 256 (accept_3_3 11 37 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 256 (accept_3_3 8 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 256 (accept_3_3 5 37 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 256 (Polychromatic418967fa.accept_22_4_15_14_1_15611 4 37 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 256 (accept_3_3 2 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  256 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 37 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 256))))))))))))))))))))))))))))))))))))) (allB_succ 36 256 (allA_succ_of_accept 35 36 256 (accept_3_3 35
  36 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 256 2 17 18 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 256 4 8 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 256 2 15 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 256 (accept_3_3 29 36 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 256 4 7 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 256 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 36 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 256 2 13 18 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 256
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 256 4 6 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 256 (accept_3_3 23 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  256 2 11 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 36 256 (Polychromatic418967fa.accept_19_2_17_9_1_10317 21 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 256 4 5 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 256 2 9 18 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 256 (accept_3_3 17 36 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 256 4 4 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 256 (Polychromatic418967fa.accept_27_15_9_13_1_13683 15 36
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 256 2 7 18 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 256
  (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 256 4 3 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 256 (accept_3_3 11 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  256 2 5 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 256 4 2 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 256 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 36 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 256 2 3 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 256 (accept_3_3 5 36 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 256 4 1 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 256 2 1 18 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 256
  (Polychromatic418967fa.accept_13_1_10_9_1_215 1 36 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 256)))))))))))))))))))))))))))))))))))) (allB_succ 35 256 (allA_of_3_1 35 35 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 256 (allA_succ_of_accept 33 34 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 256 2 16 17 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 256 2 15 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 34 256 (accept_3_3 29 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 34 256 2 14 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 34 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 256 2 13 17 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 256 2 12 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 256 (accept_3_3 23 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 256 2 11 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 256 2 10 17 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 256 2 9 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 256 (accept_3_3 17 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  256 2 8 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 256 2 7 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 34 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 256 2 6 17 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 256 (accept_3_3 11 34 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 256 2 5 17 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 256 2 4 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 256 2 3 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 256 (accept_3_3 5 34 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 256 2 2 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 256 2 1 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 256))))))))))))))))))))))))))))))))))
  (allB_succ 33 256 (allA_succ_of_accept 32 33 256 (accept_3_3 32 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 256 (accept_3_3 29 33 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28
  33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 256 (accept_3_3 26 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 256 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 256 (accept_3_3 23 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 256 (accept_3_3 20 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 256 (accept_3_3 17 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 256 (accept_3_3 14 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 256 (accept_3_3 11 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 33 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 256 (accept_3_3 8 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 256 (accept_3_3 5 33 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 33 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 256 (accept_3_3 2 33 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 256)))))))))))))))))))))))))))))))))
  (allB_succ 32 256 (allA_of_3_1 32 32 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 256
  (allA_succ_of_accept 30 31 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 256 (accept_3_3 29 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 31 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 256 (accept_3_3 26 31
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 256
  (Polychromatic418967fa.accept_10_5_1_6_1_672 25 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 256 (Polychromatic418967fa.accept_19_5_12_9_1_4588 24 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 256 (accept_3_3 23 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 256 (accept_3_3 20 31
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 256
  (Polychromatic418967fa.accept_21_19_10_4_1_14102 19 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 256 (Polychromatic418967fa.accept_19_18_12_9_1_7315 18 31 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 256 (accept_3_3 17 31 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 31 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 256 (accept_3_3 14 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 31 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 256 (accept_3_3 11 31 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 256 (accept_3_3 8 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 256 (accept_3_3 5 31 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 31 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 256 (accept_3_3 2 31 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  31 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 256)))))))))))))))))))))))))))))))
  (allB_succ 30 256 (allA_succ_of_accept 29 30 256 (accept_3_3 29 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 256 2 14 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 256 2 13 15 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 256 2 12 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 30 256 (accept_3_3 23 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 256 2 11 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 256 2 10 15 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 256 2 9 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 256 (accept_3_3 17 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30
  256 2 8 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  30 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 30 256 2 7 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 30 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 256 2 6 15 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 256 (accept_3_3 11 30 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 256 2 5 15 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 256 2 4 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 256 2 3 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 256 (accept_3_3 5 30 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 256 2 2 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 256 2 1 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 256))))))))))))))))))))))))))))))
  (allB_succ 29 256 (allA_of_3_1 29 29 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 256
  (allA_succ_of_accept 27 28 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 28 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 256 2 13 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  28 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 256 4 6 7 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 256 (accept_3_3 23
  28 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 256 2 11 14 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 256 4 5 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 28 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 256 2 9 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 256 (accept_3_3 17 28 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 256 4 4 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 28 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 256 2 7 14 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 28 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 256 4 3 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 256 (accept_3_3 11 28 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  256 2 5 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 28 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 256 4 2 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 256 2 3 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 256 (accept_3_3 5 28 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 256 4 1 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 256 2 1 14 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 256
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 28 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 256)))))))))))))))))))))))))))) (allB_succ 27 256 (allA_succ_of_accept 26 27 256 (accept_3_3 26 27 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 256 (accept_3_3 23 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 256 (Polychromatic418967fa.accept_23_22_4_3_1_15610 22 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 256 (accept_3_3 20 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 256 (accept_3_3 17 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 256 (accept_3_3 14 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 256 (accept_3_3 11 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 256 (accept_3_3 8 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 256 (accept_3_3 5 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 27 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 256 (accept_3_3 2 27 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 256))))))))))))))))))))))))))) (allB_succ 26 256
  (allA_of_3_1 26 26 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 256 (allA_succ_of_accept 24 25 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 256 (accept_3_3 23 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 256 (accept_3_3 20 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 25 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 256
  (Polychromatic418967fa.accept_19_18_6_9_1_5991 18 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 256 (accept_3_3 17 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 256 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 256 (accept_3_3 14 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 25 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 256 (accept_3_3 11 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 256 (accept_3_3 8 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 25 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 256 (accept_3_3 5 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 256 (accept_3_3 2 25 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 256))))))))))))))))))))))))) (allB_succ 24 256
  (allA_succ_of_accept 23 24 256 (accept_3_3 23 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  256 2 11 12 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 24 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 256 4 5 6 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 256 2 9 12 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 256 (accept_3_3 17 24 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 256 8 2 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 256 2 7 12 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 256 4 3 6 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 256 (accept_3_3 11 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  256 2 5 12 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 256 (Polychromatic418967fa.accept_25_9_24_6_1_15609 9 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 256 8 1 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 256 2 3 12 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 256 (accept_3_3 5 24 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 256 4 1 6 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 256 2 1 12 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 256)))))))))))))))))))))))) (allB_succ 23 256 (allA_of_3_1 23 23 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 256 (allA_succ_of_accept 21 22 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 22 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 256 2 10 11 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 256 2 9 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 256 (accept_3_3 17 22 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  256 2 8 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 256 (Polychromatic418967fa.accept_19_15_3_9_1_5962 15 22 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 256 2 7 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 22 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 256 2 6 11 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 256 (accept_3_3 11 22 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 256 2 5 11 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 256
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 22 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 256 2 4 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 256 2 3 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 256 (accept_3_3 5 22 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 256 2 2 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 256 2 1 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  22 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 256)))))))))))))))))))))) (allB_succ
  21 256 (allA_succ_of_accept 20 21 256 (accept_3_3 20 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 256 (accept_3_3 17 21 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 256 (accept_3_3 14 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 256 (accept_3_3 11 21 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 256 (accept_3_3 8 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 256 (accept_3_3 5 21 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 21 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 256 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3
  21 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 256 (accept_3_3 2 21 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 256))))))))))))))))))))) (allB_succ 20
  256 (allA_of_3_1 20 20 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 256 (allA_succ_of_accept 18 19 256
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 256 (accept_3_3 17 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 256 (accept_3_3 14 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 256 (accept_3_3 11 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 256 (accept_3_3 8 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 256 (accept_3_3 5 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  256 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 19 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 256 (accept_3_3 2 19 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 256))))))))))))))))))) (allB_succ 18 256
  (allA_succ_of_accept 17 18 256 (accept_3_3 17 18 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  256 2 8 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 18 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 256 2 7 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 256 2 6 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 256 (accept_3_3 11 18 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 256 2 5 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 18 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 256 2 4 9 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 256
  (Polychromatic418967fa.accept_21_7_18_4_1_5024 7 18 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 256 2 3 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 256 (accept_3_3 5 18 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 256
  2 2 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18
  256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 256 2 1 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 18 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 256)))))))))))))))))) (allB_succ 17 256 (allA_of_3_1 17 17 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 256 (allA_succ_of_accept 15 16 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 16 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 256 2 7 8 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 256 4 3 4 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 256 (accept_3_3 11 16 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 256 2 5 8 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 16 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 256 8 1 2 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7
  16 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 256 2 3 8 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 256 (accept_3_3 5 16
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 256 4 1 4 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 16 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 256 2 1 8 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 256)))))))))))))))) (allB_succ 15 256 (allA_succ_of_accept 14 15 256
  (accept_3_3 14 15 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 256 (accept_3_3 11 15 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 9
  15 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 256 (accept_3_3 8 15 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 256 (accept_3_3 5 15 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 15 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 256 (accept_3_3 2 15 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 256))))))))))))))) (allB_succ 14 256 (allA_of_3_1 14 14 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 256 (allA_succ_of_accept 12 13 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 256 (accept_3_3 11 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 256 (accept_3_3 8 13 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 13 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 256
  (Polychromatic418967fa.accept_19_6_13_9_1_3291 6 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 256 (accept_3_3 5 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  256 (Polychromatic418967fa.accept_19_4_13_9_1_5968 4 13 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 256 (accept_3_3 2 13 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 13 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 256))))))))))))) (allB_succ 12 256
  (allA_succ_of_accept 11 12 256 (accept_3_3 11 12 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  256 2 5 6 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  12 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 256 4 2 3 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 256 2 3 6 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 256 (accept_3_3 5 12 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 256 4 1 3 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 256 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 12 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 256 2 1 6 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 256)))))))))))) (allB_succ 11 256 (allA_of_3_1 11 11 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 256 (allA_succ_of_accept 9 10 256 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 10 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 256 2 4 5 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 256 2 3 5 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 256 (accept_3_3 5 10 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 256
  2 2 5 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10
  256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 256 2 1 5 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 256)))))))))) (allB_succ 9 256 (allA_succ_of_accept 8 9 256 (accept_3_3 8
  9 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 9 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 256 (accept_3_3 5 9 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 256
  (Polychromatic418967fa.accept_24_4_9_16_1_15608 4 9 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 9 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 256 (accept_3_3 2 9 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 256))))))))) (allB_succ 8 256 (allA_of_3_1 8 8 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 256 (allA_succ_of_accept 6 7 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 256 (accept_3_3 5 7 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 256
  (Polychromatic418967fa.accept_11_4_7_3_1_289 4 7 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 256 (accept_3_3 2 7 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 256))))))) (allB_succ 6 256 (allA_succ_of_accept 5 6 256
  (accept_3_3 5 6 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 256 2 2 3 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 256 2 1 3 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 256)))))) (allB_succ 5 256 (allA_of_3_1 5 5 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 256 (allA_succ_of_accept 3 4 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 4
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 256 2 1 2 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 256
  (Polychromatic418967fa.accept_23_1_4_3_1_15607 1 4 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 256)))) (allB_succ 3 256 (allA_succ_of_accept 2 3 256 (accept_3_3 2 3 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 256))) (allB_succ 2 256 (allA_of_3_1 2 2 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


