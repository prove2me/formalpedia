-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch286_Segment000
-- name    : Polychromatic418967fa_Branch286_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:54:13.785089+00:00
-- url     : https://prove2.me/theorems/4fa02324-eea5-42c6-8c45-b367213764cc
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

def Polychromatic418967fa.branch_286_segment_000 : allB 124 286 :=
  allB_succ 123 286 (allA_succ_of_accept 122 123 286 (accept_3_3 122 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 123 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 120 123
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 286 (accept_3_3 119 123
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 118 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 123 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 286 (accept_3_3 116 123 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 286 (Polychromatic418967fa.accept_7_2_4_6_1_166
  114 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 286 (accept_3_3
  113 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 112 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 123 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 111 123 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 286 (accept_3_3 110 123 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329
  108 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 286 (accept_3_3
  107 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 286
  (Polychromatic418967fa.accept_19_11_9_1_1_2809 106 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 286 (accept_3_3 104 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 102 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 123 286 (accept_3_3 101 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 123 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 123 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 99 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 286 (accept_3_3 98 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 123 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 96 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 286 (accept_3_3 95 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 286 (accept_3_3 92 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 286 (accept_3_3 89 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 286 (accept_3_3 86 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 286 (accept_3_3 83 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 286 (accept_3_3 80 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 78 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 286 (accept_3_3 77 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 286 (accept_3_3 74 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 286 (accept_3_3 71 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 286 (Polychromatic418967fa.accept_21_7_18_13_1_5585 70 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 286 (accept_3_3 68 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 286 (accept_3_3 65 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 286 (Polychromatic418967fa.accept_18_9_15_16_1_8759 63 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 286 (accept_3_3 62 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 123 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 60 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 286 (accept_3_3 59 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 286 (accept_3_3 56 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 286 (accept_3_3 53 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 286 (accept_3_3 50 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 286 (accept_3_3 47 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 286 (accept_3_3 44 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 286 (accept_3_3 41 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 286 (accept_3_3 38 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 286 (accept_3_3 35 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 286 (accept_3_3 32 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 286 (accept_3_3 29 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 286 (accept_3_3 26 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 286 (accept_3_3 23 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 286 (accept_3_3 20 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 286 (accept_3_3 17 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 286 (Polychromatic418967fa.accept_21_15_18_13_1_8747 15 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 286 (accept_3_3 14 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 286 (accept_3_3 11 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 286 (accept_3_3 8 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 286 (accept_3_3 5 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 286 (accept_3_3 2 123 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 286 (allA_of_3_1 122 122 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 286
  (allA_succ_of_accept 120 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 286 (accept_3_3 119 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 118 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25
  117 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 121 286 (accept_3_3
  116 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 115 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 121 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 114 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 286 (accept_3_3 113 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 121 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 121 286 11 10 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 121 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 109 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 286 (accept_3_3 107 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 105 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 286 (accept_3_3 104 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 121
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 121 286 (accept_3_3 101 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 121 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 121 286 11 9 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 121 286 (accept_3_3 98 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 121 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 97 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 121 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 286 (accept_3_3 95 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 94
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 286 (accept_3_3 92 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 286 (Polychromatic418967fa.accept_17_5_2_14_1_4270 90 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 286 (accept_3_3 89 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 121 286 11 8 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 286 (accept_3_3 86
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 121 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 286 (accept_3_3 83 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 121 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 81
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 286 (accept_3_3 80
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 121 286 11 7 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 121 286 (Polychromatic418967fa.accept_12_4_1_10_1_221
  76 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 286 (accept_3_3 74 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 286 (accept_3_3 71 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 286 (Polychromatic418967fa.accept_19_13_7_1_1_5379 70 121
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 286 (accept_3_3 68 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 121 286 11 6 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 121 286 (accept_3_3 65 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 286 (accept_3_3 62 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 286 (Polychromatic418967fa.accept_19_4_7_1_1_1683
  61 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 286 (accept_3_3 59 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 286 (Polychromatic418967fa.accept_23_12_6_10_1_17553 58 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 286 (accept_3_3 56 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 121 286 11 5 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 121 286 (Polychromatic418967fa.accept_17_3_2_14_1_6714
  54 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 286 (accept_3_3 53
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 286 (accept_3_3 50 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 121 286 (Polychromatic418967fa.accept_21_7_16_13_1_2733 49 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 286 (accept_3_3 47 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 121 286 11 4 11 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 121 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 286 (accept_3_3 41 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 121 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 286 (accept_3_3 38 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 286 (accept_3_3 35 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 286 (Polychromatic418967fa.accept_20_14_1_6_1_3352 34 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 121 286 11 3 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 121 286 (accept_3_3 32
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 121 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 286 (accept_3_3 29 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 121 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 286 (accept_3_3 26
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 121 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 286 (accept_3_3 23 121 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 121 286 11 2 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 286 (accept_3_3 20 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 286 (accept_3_3 17 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 286 (accept_3_3 14 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 286 (Polychromatic418967fa.accept_19_13_7_1_1_5379 13 121 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 121 286 11 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 121 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9
  121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 286 (accept_3_3 8 121
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 286 (accept_3_3 5 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 286 (accept_3_3 2 121 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 286 (allA_succ_of_accept 119 120 286 (accept_3_3 119 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 120 286 2 59 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 120 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 286 2 58 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 286
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 115 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 120 286 2 57 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 120 286 (accept_3_3 113 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 120 286 2 56 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 120 286 (Polychromatic418967fa.accept_21_6_15_13_1_13252 111 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 286 2 55 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 109 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 286 2 54 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 286 (accept_3_3 107 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 286 2 53 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 120 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 120 286 2 52 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 286 2 51 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 286 (accept_3_3 101 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 286 2 50 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 99 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 286 2 49 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 286
  (Polychromatic418967fa.accept_19_2_6_1_1_9729 97 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 286 2 48 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 286 (accept_3_3 95 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 120 286 2 47 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 120 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 286 2 46 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 286 2 45 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 286 (accept_3_3 89 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 286 2 44 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 286 2 43 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 286 2 42 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 286 (accept_3_3 83 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 286 2 41 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 120 286 (Polychromatic418967fa.accept_17_13_1_14_1_1149 81 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 286 2 40 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 286 2 39 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 286 (accept_3_3 77 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 286 2 38 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 120 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 120 286 2 37 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 286 2 36 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 286 (accept_3_3 71 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 286 2 35 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 286 2 34 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 286 2 33 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 286 (accept_3_3 65 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 286 2 32 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 120 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 286 2 31 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 286 2 30 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 286 (accept_3_3 59 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 286 2 29 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 120 286 (Polychromatic418967fa.accept_23_11_5_10_1_17552 57 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 286 2 28 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 286 2 27 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 286 (accept_3_3 53 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 286 2 26 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 286 2 25 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 286 2 24 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 286 (accept_3_3 47 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 286 2 23 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 45 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 286 2 22 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 286
  (Polychromatic418967fa.accept_19_5_6_1_1_5366 43 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 286 2 21 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 286 (accept_3_3 41 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 286 2 20 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 286 (Polychromatic418967fa.accept_21_18_15_13_1_4130 39 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 286 2 19 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 286 2 18 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 286 (accept_3_3 35 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 286 2 17 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 286 2 16 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 286 2 15 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 286 (accept_3_3 29 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 286 2 14 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 286 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 286 2 13 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 286
  (Polychromatic418967fa.accept_33_25_21_22_1_17551 25 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 120 286 2 12 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 286 (accept_3_3 23 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 286 2 11 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 286 2 10 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 286 2 9 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 286 (accept_3_3 17 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 286 2 8 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 120 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 286 2 7 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 286 2 6 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 120 286 (accept_3_3 11 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 286 2 5 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 286 2 4 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 286 2 3 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 286 (accept_3_3 5 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120
  286 2 2 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  120 286 (Polychromatic418967fa.accept_19_3_6_1_1_4064 3 120 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 120 286 2 1 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 120 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 286 (allA_of_3_1 119 119 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 286
  (allA_succ_of_accept 117 118 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 117 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 286 2 58 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 115 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 118 286 2 57 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 118 286 (accept_3_3 113 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 286 2 56 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 111 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 286 2 55 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 109 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 118 286 2 54 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 118 286 (accept_3_3 107 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 286 2 53 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 105 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 286 2 52 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 103 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 286 2 51 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 286 (accept_3_3 101 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 286 2 50 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 286 (Polychromatic418967fa.accept_23_7_3_10_1_2935 99 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 286 2 49 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 286
  (Polychromatic418967fa.accept_23_5_3_10_1_14441 97 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 118 286 2 48 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 118 286 (accept_3_3 95 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 286 2 47 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 93 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 286 2 46 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 91 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 286 2 45 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 286 (accept_3_3 89 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 286 2 44 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 286 2 43 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 286 2 42 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 286 (accept_3_3 83 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 286 2 41 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 286 (Polychromatic418967fa.accept_19_5_4_1_1_12396 81 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 286 2 40 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 286
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 79 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 118 286 2 39 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 118 286 (accept_3_3 77 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 286 2 38 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 286 2 37 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 286 2 36 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 286 (accept_3_3 71 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 286 2 35 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 286 2 34 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 286 2 33 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 286 (accept_3_3 65 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 286 2 32 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 286 2 31 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 286
  (Polychromatic418967fa.accept_27_7_10_16_1_17515 61 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 118 286 2 30 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 118 286 (accept_3_3 59 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 286 2 29 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 286 2 28 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 118 286 2 27 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 118 286 (accept_3_3 53 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 286 2 26 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 286 2 25 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 286 2 24 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 286 (accept_3_3 47 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 286 2 23 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 286 (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 286 2 22 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 286 2 21 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 286 (accept_3_3 41 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 286 2 20 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 286 2 19 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 286 2 18 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 286 (accept_3_3 35 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 286 2 17 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 286 2 16 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 286 2 15 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 286 (accept_3_3 29 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 286 2 14 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 286 2 13 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 118 286 2 12 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 118 286 (accept_3_3 23 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 286 2 11 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 286 2 10 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 286
  (Polychromatic418967fa.accept_17_2_16_14_1_2116 19 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 118 286 2 9 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 118 286 (accept_3_3 17 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 286 2 8 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 118 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 286 2 7 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 286 2 6 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 286 (accept_3_3 11 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 286 2 5 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 286 (Polychromatic418967fa.accept_33_9_19_22_1_17550 9 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 286 2 4 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 286
  (Polychromatic418967fa.accept_19_7_4_1_1_5399 7 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 286 2 3 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 286 (accept_3_3 5 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  286 2 2 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 286 2 1 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 118 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 286 (allA_succ_of_accept 116 117 286 (accept_3_3 116 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 114 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 286 (accept_3_3 113 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 286
  (Polychromatic418967fa.accept_19_17_3_1_1_4056 112 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 286 (accept_3_3 110 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 286
  (Polychromatic418967fa.accept_17_6_15_14_1_8027 108 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 117 286 (accept_3_3 107 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 106 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 105
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 117 286 13 8 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 117 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 286 (accept_3_3 101 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 286 (Polychromatic418967fa.accept_19_5_3_1_1_4055 100 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 286 (accept_3_3 98 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 286 (Polychromatic418967fa.accept_20_16_17_6_1_7799 96 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 286 (accept_3_3 95 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 94 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 286
  (Polychromatic418967fa.accept_10_3_7_6_1_659 93 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 286 (accept_3_3 92 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  117 286 13 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  90 117 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 286 (accept_3_3 89 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 286 (accept_3_3 86 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 286
  (Polychromatic418967fa.accept_17_16_15_14_1_6747 84 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 286 (accept_3_3 83 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 286 (Polychromatic418967fa.accept_19_6_3_1_1_2824 82 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 286 (accept_3_3 80 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 286 13 6 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 286 (accept_3_3 77
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 286
  (Polychromatic418967fa.accept_20_16_17_6_1_7799 76 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 286 (accept_3_3 74 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 286
  (Polychromatic418967fa.accept_20_12_17_6_1_9194 72 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 286 (accept_3_3 71 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 286 (Polychromatic418967fa.accept_28_14_5_6_1_17549 70 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 286
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 69 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 286 (accept_3_3 68 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 117 286 13 5 9 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 64 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 286 (accept_3_3 62 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344
  60 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 286 (accept_3_3 59
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 286 (accept_3_3 56 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 286 (accept_3_3 53 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52
  117 286 13 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 286 (accept_3_3 50 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 286 (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 286 (accept_3_3 47 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 117 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 45 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 286 (accept_3_3 44 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 286 (accept_3_3 41 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 286 (Polychromatic418967fa.accept_17_6_15_14_1_8027 40 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 117 286 13 3 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 117 286 (accept_3_3 38 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 286 (accept_3_3 35 117 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 286
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 117 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 286 (accept_3_3 32 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 286 (Polychromatic418967fa.accept_12_6_9_10_1_565
  30 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 286 (accept_3_3 29
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 117 286 13 2 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 117 286 (Polychromatic418967fa.accept_19_5_3_1_1_4055 24 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 286 (accept_3_3 23 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 286 (Polychromatic418967fa.accept_10_1_7_6_1_91
  21 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 286 (accept_3_3 20
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 286 (accept_3_3 17 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 117 286 (Polychromatic418967fa.accept_17_16_15_14_1_6747 16 117 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 286 (accept_3_3 14 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  117 286 13 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  12 117 286 (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 286 (accept_3_3 11 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 286 (Polychromatic418967fa.accept_16_10_5_14_1_6173 10 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126
  9 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 286 (accept_3_3 8
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 117 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 286 (accept_3_3 5 117 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 117 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 286 (accept_3_3 2 117
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 117 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 286 (allA_of_3_1 116 116 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 286
  (allA_succ_of_accept 114 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 115 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 286 (accept_3_3 113 115 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 112 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 286 (accept_3_3 110 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 108 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 286 (accept_3_3 107 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 286 (Polychromatic418967fa.accept_17_4_13_14_1_1139 106
  115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 286 (accept_3_3 104 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 103 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 286 (accept_3_3 101 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 115 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 286 (accept_3_3 98 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 96 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 286 (accept_3_3 95 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 286 (accept_3_3 92 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 91 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 286 (Polychromatic418967fa.accept_20_10_15_6_1_2149 90 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 286 (accept_3_3 89 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 115 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 286 (accept_3_3 86 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 286 (accept_3_3 83 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 82 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 286 (accept_3_3 80 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 286 (Polychromatic418967fa.accept_17_10_13_14_1_3094 78 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 286 (accept_3_3 77 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 286 (accept_3_3 74 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 286 (accept_3_3 71 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 286 (Polychromatic418967fa.accept_20_10_15_6_1_2149 70 115 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 286 (accept_3_3 68 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 66 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 286 (accept_3_3 65 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 286 (accept_3_3 62 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 286 (accept_3_3 59 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 286 (accept_3_3 56 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 286 (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 286 (accept_3_3 53 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 286 (accept_3_3 50 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 286 (Polychromatic418967fa.accept_27_21_7_16_1_17548 48 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 286 (accept_3_3 47 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 115 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 286 (accept_3_3 44 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 286 (Polychromatic418967fa.accept_27_15_7_16_1_17547 42 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 286 (accept_3_3 41 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 286 (accept_3_3 38 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 286 (accept_3_3 35 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 286 (accept_3_3 32 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 286 (accept_3_3 29 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 286 (accept_3_3 26 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 286 (accept_3_3 23 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 286 (accept_3_3 20 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 286 (accept_3_3 17 115 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 286 (accept_3_3 14 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 286 (Polychromatic418967fa.accept_20_12_15_6_1_9201 12 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 286 (accept_3_3 11 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 115
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 286 (accept_3_3 8 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 286 (accept_3_3 5 115 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 286 (accept_3_3 2 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 286 (allA_succ_of_accept 113 114 286 (accept_3_3 113 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 114 286 2 56 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 114 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 111 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 286 2 55 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 109 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 286 2 54 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 286 (accept_3_3 107 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 286 2 53 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 105 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 286 2 52 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 103 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 286 2 51 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 286 (accept_3_3 101 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 286 2 50 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 286 2 49 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 97 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 286 2 48 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 286 (accept_3_3 95 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 286 2 47 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 286 2 46 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 286 2 45 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 286 (accept_3_3 89 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 286 2 44 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 286 2 43 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 286 2 42 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 286 (accept_3_3 83 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 286 2 41 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 286 2 40 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 286
  (Polychromatic418967fa.accept_17_11_12_14_1_5431 79 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 114 286 2 39 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 114 286 (accept_3_3 77 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 286 2 38 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 286 2 37 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 286 2 36 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 286 (accept_3_3 71 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 286 2 35 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 286 2 34 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 286 2 33 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 286 (accept_3_3 65 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 286 2 32 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 286 2 31 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 286
  (Polychromatic418967fa.accept_20_1_14_6_1_4725 61 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 286 2 30 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 286 (accept_3_3 59 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 286 2 29 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 286 2 28 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 286 2 27 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 286 (accept_3_3 53 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 286 2 26 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 286 2 25 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 286 2 24 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 286 (accept_3_3 47 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 286 2 23 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 286 2 22 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 286 2 21 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 286 (accept_3_3 41 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 286 2 20 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 286 2 19 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 286 2 18 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 286 (accept_3_3 35 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 286 2 17 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 286 2 16 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 286 2 15 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 286 (accept_3_3 29 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 286 2 14 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 286 2 13 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 286 2 12 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 286 (accept_3_3 23 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 286 2 11 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 286 2 10 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 286 2 9 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 286 (accept_3_3 17 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 286 2 8 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 286 2 7 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 286 2 6 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 286 (accept_3_3 11 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 286 2 5 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 286 2 4 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 286 2 3 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 286 (accept_3_3 5 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114
  286 2 2 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  114 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 114 286 2 1 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 114 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 286 (allA_of_3_1 113 113 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 286
  (allA_succ_of_accept 111 112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 111 112 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 286 2 55 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 109
  112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 112 286 2 54 56 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 112 286
  (accept_3_3 107 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 112 286 2 53 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 112 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 105 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 112 286 2 52 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 112 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 103 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 112 286 2 51 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 112 286 (accept_3_3 101 112 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 112 286 2 50 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 112 286
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 99 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 112 286 2 49 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 112 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 112 286 2 48 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 112 286 (accept_3_3 95 112 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 112 286 2 47 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 112 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 112 286 2 46 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 112 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 112 286 2 45 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 286 (accept_3_3 89 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 112 286 2 44 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 112 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 286 2 43 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 85 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 286 2 42 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 286 (accept_3_3 83 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 286 2 41 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 286 2 40 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 286 2 39 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 286 (accept_3_3 77 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 286 2 38 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 286 2 37 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 286 2 36 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 112 286 (accept_3_3 71 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 286 2 35 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 286 2 34 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 112 286 2 33 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 112 286 (accept_3_3 65 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 286 2 32 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 286 (Polychromatic418967fa.accept_31_1_19_7_1_17546 63 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 286 2 31 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 286 2 30 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 286 (accept_3_3 59 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 286 2 29 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 286 2 28 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 286 2 27 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 286 (accept_3_3 53 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 286 2 26 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 286 2 25 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 286 2 24 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 286 (accept_3_3 47 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 286 2 23 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 286 (Polychromatic418967fa.accept_20_5_12_6_1_7806 45 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 286 2 22 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 286 2 21 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 286 (accept_3_3 41 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 286 2 20 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 286 2 19 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 286 2 18 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 286 (accept_3_3 35 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 286 2 17 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 286 2 16 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 286 2 15 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 286 (accept_3_3 29 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 286 2 14 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 286 (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 286 2 13 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 286 2 12 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 286 (accept_3_3 23 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 286 2 11 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 286 2 10 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 286 2 9 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 286 (accept_3_3 17 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 286 2 8 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 112 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 286 2 7 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 112 286 2 6 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 112 286 (accept_3_3 11 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 286 2 5 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 112 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 286 2 4 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 286 2 3 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 286 (accept_3_3 5 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  286 2 2 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 286 2 1 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 112 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 286 (allA_succ_of_accept 110 111 286 (accept_3_3 110 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 108 111
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 286 (accept_3_3 107 111
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 286
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 106 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 286 (accept_3_3 104 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 102 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 286 (accept_3_3 101 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 100 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 99 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 286 (accept_3_3 98 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 111 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 286 (accept_3_3 95 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 286 (accept_3_3 92 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 286 (accept_3_3 89 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 286 (Polychromatic418967fa.accept_21_4_6_13_1_7137 88 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 286 (accept_3_3 86 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 84 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 286 (accept_3_3 83 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 286 (accept_3_3 80 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 286 (accept_3_3 77 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 75 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 286 (accept_3_3 74 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 286 (accept_3_3 71 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 286 (accept_3_3 68 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 286 (accept_3_3 65 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 286 (Polychromatic418967fa.accept_14_7_13_6_1_1177 63 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 286 (accept_3_3 62 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 286 (accept_3_3 59 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 286 (accept_3_3 56 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 286 (accept_3_3 53 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 286 (accept_3_3 50 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 286 (accept_3_3 47 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 286 (accept_3_3 44 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 286 (accept_3_3 41 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 286 (accept_3_3 38 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 286
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 286 (accept_3_3 35 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 286 (Polychromatic418967fa.accept_19_15_16_1_1_11087 34 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 286 (accept_3_3 32
  111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 111 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 286 (accept_3_3 29 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 286 (Polychromatic418967fa.accept_10_7_1_6_1_673
  27 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 286 (accept_3_3 26
  111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 286 (accept_3_3 23 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 286 (accept_3_3 20
  111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 111 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 286 (accept_3_3 17 111 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 286 (Polychromatic418967fa.accept_20_16_11_6_1_10684 16 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 286 (accept_3_3 14 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 286 (accept_3_3 11 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 286 (accept_3_3 8 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 286 (accept_3_3 5 111 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 111 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 286 (accept_3_3 2 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 286 (allA_of_3_1 110 110 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 286
  (allA_succ_of_accept 108 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 109 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 286 (accept_3_3 107 109 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 106 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 286 (accept_3_3 104 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 286 (accept_3_3 101 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 109
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 286 (accept_3_3 98 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 97 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 286 (accept_3_3 95 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 286 (accept_3_3 92 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 90 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 286 (accept_3_3 89 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 109
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 286 (accept_3_3 86 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 286 (accept_3_3 83 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 286 (accept_3_3 80 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 286 (accept_3_3 77 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 286 (accept_3_3 74 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 286 (accept_3_3 71 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 286 (Polychromatic418967fa.accept_19_13_14_1_1_3996 70 109 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 286 (accept_3_3 68 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 286 (accept_3_3 65 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 286 (accept_3_3 62 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 286 (accept_3_3 59 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 286 (accept_3_3 56 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 286 (accept_3_3 53 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 286 (accept_3_3 50 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 286 (accept_3_3 47 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 109 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 286 (accept_3_3 44 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 286 (accept_3_3 41 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 286 (accept_3_3 38 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 286 (Polychromatic418967fa.accept_19_17_14_1_1_6825 36 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 286 (accept_3_3 35 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 286 (Polychromatic418967fa.accept_19_15_14_1_1_8297 34 109
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 286 (accept_3_3 32 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 286 (accept_3_3 29 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 286 (accept_3_3 26 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 286 (accept_3_3 23 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 286 (accept_3_3 20 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 286 (accept_3_3 17 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 286 (accept_3_3 14 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 286 (accept_3_3 11 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 286 (accept_3_3 8 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 286 (accept_3_3 5 109 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 286 (accept_3_3 2 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 109 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 286 (allA_succ_of_accept 107 108 286 (accept_3_3 107 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 108 286 2 53 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 108 286 (Polychromatic418967fa.accept_17_3_6_14_1_4312 105 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 286 2 52 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 103 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 286 2 51 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 286 (accept_3_3 101 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 108 286 2 50 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 108 286 (Polychromatic418967fa.accept_23_7_16_10_1_14382 99 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 286 2 49 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 286
  (Polychromatic418967fa.accept_19_2_13_1_1_6831 97 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 286 2 48 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 286 (accept_3_3 95 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 286 2 47 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 286 2 46 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 286
  (Polychromatic418967fa.accept_23_22_16_10_1_17545 91 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 108 286 2 45 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 286 (accept_3_3 89 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 286 2 44 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 87 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 286 2 43 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 286
  (Polychromatic418967fa.accept_25_10_8_11_1_17544 85 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 108 286 2 42 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 108 286 (accept_3_3 83 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 286 2 41 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 286 2 40 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 286 2 39 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 286 (accept_3_3 77 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 286 2 38 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 286 (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 286 2 37 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 286 2 36 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 286 (accept_3_3 71 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 286 2 35 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 286 (Polychromatic418967fa.accept_19_12_13_1_1_2779 69 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 286 2 34 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 286 2 33 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 286 (accept_3_3 65 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 286 2 32 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 286 2 31 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 286
  (Polychromatic418967fa.accept_29_3_21_25_1_17543 61 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 286 2 30 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 286 (accept_3_3 59 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 286 2 29 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 286 (Polychromatic418967fa.accept_28_1_24_6_1_17542 57 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 286 2 28 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 286
  (Polychromatic418967fa.accept_25_5_8_11_1_12468 55 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 108 286 2 27 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 108 286 (accept_3_3 53 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 286 2 26 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 286 2 25 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 49 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 286 2 24 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 286 (accept_3_3 47 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 286 2 23 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 286 2 22 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 286 2 21 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 286 (accept_3_3 41 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 286 2 20 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 286 2 19 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 286 2 18 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 286 (accept_3_3 35 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 286 2 17 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 286 2 16 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 286 2 15 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 286 (accept_3_3 29 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 286 2 14 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 286 (Polychromatic418967fa.accept_19_8_13_1_1_8221 27 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 286 2 13 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 286 2 12 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 286 (accept_3_3 23 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 286 2 11 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 286 2 10 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 286 2 9 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 286 (accept_3_3 17 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 286 2 8 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 108 286 (Polychromatic418967fa.accept_17_15_6_14_1_4239 15 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 286 2 7 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 286 2 6 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 108 286 (accept_3_3 11 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 286 2 5 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 286 2 4 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 286
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 286 2 3 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 286 (accept_3_3 5 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108
  286 2 2 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  108 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 108 286 2 1 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 108 286 (Polychromatic418967fa.accept_28_1_24_6_1_17542 1 108 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 286 (allA_of_3_1 107 107 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 286
  (allA_succ_of_accept 105 106 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 105 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 286 2 52 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 106 286 2 51 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 106 286 (accept_3_3 101 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 106 286 2 50 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 106 286 (Polychromatic418967fa.accept_23_7_14_10_1_17541 99 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 106 286 2 49 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 106 286
  (Polychromatic418967fa.accept_25_22_6_11_1_17540 97 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 106 286 2 48 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 106 286 (accept_3_3 95 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 106 286 2 47 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 106 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 286 2 46 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 91 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 286 2 45 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 286 (accept_3_3 89 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 286 2 44 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 87 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 286 2 43 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 286
  (Polychromatic418967fa.accept_16_5_10_14_1_5074 85 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 106 286 2 42 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 106 286 (accept_3_3 83 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 286 2 41 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 286 (Polychromatic418967fa.accept_17_13_4_14_1_4272 81 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 286 2 40 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 286 2 39 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 286 (accept_3_3 77 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 286 2 38 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 286 2 37 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 286
  (Polychromatic418967fa.accept_21_10_1_13_1_7167 73 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 106 286 2 36 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 106 286 (accept_3_3 71 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 286 2 35 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 286 (Polychromatic418967fa.accept_16_5_10_14_1_5074 69 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 286 2 34 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 286
  (Polychromatic418967fa.accept_19_10_11_1_1_8318 67 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 106 286 2 33 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 106 286 (accept_3_3 65 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 286 2 32 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 286 2 31 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 286 2 30 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 286 (accept_3_3 59 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 286 2 29 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 286 (Polychromatic418967fa.accept_27_3_25_16_1_17539 57 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 286 2 28 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 286
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 55 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 106 286 2 27 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 106 286 (accept_3_3 53 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 286 2 26 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 286 2 25 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 286 2 24 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 286 (accept_3_3 47 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 286 2 23 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 286 (Polychromatic418967fa.accept_16_13_10_14_1_2871 45 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 286 2 22 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 43 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 286 2 21 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 286 (accept_3_3 41 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 286 2 20 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 39 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 286 2 19 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 286 2 18 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 286 (accept_3_3 35 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 286 2 17 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 286 2 16 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 286
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 106 286 2 15 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 106 286 (accept_3_3 29 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 286 2 14 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 286 (Polychromatic418967fa.accept_19_8_11_1_1_8320 27 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 286 2 13 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 286
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 25 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 286 2 12 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 286 (accept_3_3 23 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 286 2 11 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 286 2 10 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 286 2 9 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 286 (accept_3_3 17 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 286 2 8 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 286 (Polychromatic418967fa.accept_16_15_10_14_1_2872 15 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 286 2 7 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 286
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 106 286 2 6 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 106 286 (accept_3_3 11 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 286 2 5 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 106 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 286 2 4 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 286 2 3 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 286 (accept_3_3 5 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  286 2 2 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 286 (Polychromatic418967fa.accept_19_3_11_1_1_8319 3 106 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 286 2 1 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 286 (Polychromatic418967fa.accept_17_1_4_14_1_8058 1 106 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 286 (allA_succ_of_accept 104 105 286 (accept_3_3 104 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 105 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 105
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 286 (accept_3_3 101 105
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 100 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 286 (accept_3_3 98 105 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 286
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 96 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 105 286 (accept_3_3 95 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 105 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 286 (accept_3_3 92 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91
  105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 90 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 286 (accept_3_3 89 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 286 (Polychromatic418967fa.accept_23_19_13_10_1_11249 88 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 286 (accept_3_3 86 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 286 (accept_3_3 83 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 286 (accept_3_3 80 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 78 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 286 (accept_3_3 77 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 286 (accept_3_3 74 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 286
  (Polychromatic418967fa.accept_20_12_5_6_1_6205 72 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 286 (accept_3_3 71 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 286 (Polychromatic418967fa.accept_17_2_3_14_1_8043 70 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 286 (accept_3_3 68 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 286 (accept_3_3 65 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 286 (accept_3_3 62 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 286
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 286 (accept_3_3 59 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 105 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 286 (accept_3_3 56 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 286 (accept_3_3 53 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 52 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 286 (accept_3_3 50 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 286 (accept_3_3 47 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 286 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 286 (accept_3_3 44 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 286 (accept_3_3 41 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 286 (accept_3_3 38 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 286 (accept_3_3 35 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 286 (Polychromatic418967fa.accept_19_14_10_1_1_8316 33 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 286 (accept_3_3 32 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 286 (accept_3_3 29 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 286 (accept_3_3 26 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 286 (accept_3_3 23 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 286 (accept_3_3 20 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 286 (accept_3_3 17 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 286 (Polychromatic418967fa.accept_19_16_10_1_1_11073 16 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 286 (accept_3_3 14 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 286 (accept_3_3 11 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 286 (accept_3_3 8 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 286 (accept_3_3 5 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 286 (accept_3_3 2 105 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 286 (allA_of_3_1 104 104 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 286
  (allA_succ_of_accept 102 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 103 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 286 (accept_3_3 101 103 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 99
  103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 103 286 (accept_3_3 98
  103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 103 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 103 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 286 (accept_3_3 95 103 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 103 286 (Polychromatic418967fa.accept_19_18_8_1_1_11071 94 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 286 (accept_3_3 92 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 286 (Polychromatic418967fa.accept_16_10_7_14_1_2882 90 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 286 (accept_3_3 89 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 103 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 286 (accept_3_3 86 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 286 (accept_3_3 83 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 286 (accept_3_3 80 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 79 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 286 (accept_3_3 77 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 286 (accept_3_3 74 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 286 (accept_3_3 71 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 103
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 286 (accept_3_3 68 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 286 (accept_3_3 65 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 286 (accept_3_3 62 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 286 (accept_3_3 59 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 286 (accept_3_3 56 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 286 (Polychromatic418967fa.accept_19_16_8_1_1_8259 54 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 286 (accept_3_3 53 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 103
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 286 (accept_3_3 50 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 286 (accept_3_3 47 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 286 (accept_3_3 44 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 286 (accept_3_3 41 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 286 (accept_3_3 38 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 286 (accept_3_3 35 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 286 (Polychromatic418967fa.accept_19_15_8_1_1_6794 34 103 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 286 (accept_3_3 32 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 286 (Polychromatic418967fa.accept_16_15_7_14_1_2883 31 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 286 (accept_3_3 29 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 286 (accept_3_3 26 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 286 (accept_3_3 23 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 286 (accept_3_3 20 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 286 (accept_3_3 17 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 286 (accept_3_3 14 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 286 (accept_3_3 11 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 286 (accept_3_3 8 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 286 (accept_3_3 5 103 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 286 (accept_3_3 2 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 286 (allA_succ_of_accept 101 102 286 (accept_3_3 101 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 286 2 50 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 99 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 286 2 49 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 286
  (Polychromatic418967fa.accept_19_2_7_1_1_2808 97 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 286 2 48 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 286 (accept_3_3 95 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 286 2 47 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 286 2 46 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 286 2 45 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 286 (accept_3_3 89 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 286 2 44 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 286 2 43 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 286 2 42 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 286 (accept_3_3 83 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 286 2 41 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 286 2 40 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 286 2 39 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 286 (accept_3_3 77 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 286 2 38 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 286 2 37 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 286 2 36 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 286 (accept_3_3 71 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 286 2 35 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 286 2 34 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 286 2 33 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 286 (accept_3_3 65 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 286 2 32 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 286 2 31 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 286 2 30 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 286 (accept_3_3 59 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 286 2 29 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 286 2 28 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 286 2 27 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 286 (accept_3_3 53 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 286 2 26 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 286 2 25 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 286 2 24 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 286 (accept_3_3 47 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 286 2 23 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 286 2 22 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 286 2 21 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 286 (accept_3_3 41 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 286 2 20 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 286 2 19 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 286 2 18 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 286 (accept_3_3 35 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 286 2 17 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 286 2 16 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 286 2 15 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 286 (accept_3_3 29 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 286 2 14 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 286 2 13 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 286
  (Polychromatic418967fa.accept_19_6_7_1_1_2805 25 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 286 2 12 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 286 (accept_3_3 23 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 286 2 11 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 286 2 10 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 286 2 9 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 286 (accept_3_3 17 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 286 2 8 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 286 2 7 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 286 2 6 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 286 (accept_3_3 11 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 286 2 5 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 286 2 4 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 286
  (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 286 2 3 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 286 (accept_3_3 5 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  286 2 2 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 286 2 1 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 286 (allA_of_3_1 101 101 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 286 (allA_succ_of_accept 99
  100 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 286 2 49 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 286 2 48 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 100 286 (accept_3_3 95 100 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 100 286 2 47 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 93 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 286 2 46 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 286 2 45 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 286 (accept_3_3 89 100 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 286 2 44 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 286 2 43 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 100 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 100 286 2 42 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 286 (accept_3_3 83 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 100 286 2 41 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 100 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81
  100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 286 2 40 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 286 2 39 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 286 (accept_3_3 77 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 286 2 38 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 286 2 37 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 286 2 36 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 286 (accept_3_3 71 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 286 2 35 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 286 2 34 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 286 2 33 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 286 (accept_3_3 65 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 286 2 32 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 286 2 31 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 286 2 30 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 286 (accept_3_3 59 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 286 2 29 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 286 2 28 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 286 2 27 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 286 (accept_3_3 53 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 286 2 26 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 286 2 25 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 286 2 24 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 286 (accept_3_3 47 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 286 2 23 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 286 2 22 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 286 2 21 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 286 (accept_3_3 41 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 286 2 20 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 286 2 19 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 286 2 18 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 286 (accept_3_3 35 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 286 2 17 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 286 2 16 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 286 2 15 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 286 (accept_3_3 29 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 286 2 14 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 286 (Polychromatic418967fa.accept_21_6_16_13_1_4100 27 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 286 2 13 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 286 2 12 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 286 (accept_3_3 23 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 286 2 11 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 286 2 10 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 286 2 9 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 100 286 (accept_3_3 17 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 286 2 8 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 100 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 286 2 7 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 286 2 6 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 100 286 (accept_3_3 11 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 286 2 5 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 286 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 100 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 286 2 4 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 286 2 3 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 286 (accept_3_3 5 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  286 2 2 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 286 2 1 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 100 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  286 (allA_succ_of_accept 98 99 286 (accept_3_3 98 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 286 (accept_3_3 95 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 94 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 286 (accept_3_3 92 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 90 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 286 (accept_3_3 89 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 286 11 8 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 99 286 (Polychromatic418967fa.accept_18_15_9_16_1_6029 87 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 286 (accept_3_3 86 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 84 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 99 286 (accept_3_3 83 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 286 (accept_3_3 80 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 78 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 99 286 11 7 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 99 286 (Polychromatic418967fa.accept_25_1_24_11_1_15903 76 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 286 (accept_3_3 74 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 99 286 (accept_3_3 71 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  99 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 286 (accept_3_3 68 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 286 11 6 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 286 (accept_3_3 65 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 286 (Polychromatic418967fa.accept_19_7_4_1_1_5399 64 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 286
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 286 (accept_3_3 62 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 286 (Polychromatic418967fa.accept_19_3_4_1_1_9733 60 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 286 (accept_3_3 59 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 286 (accept_3_3 56 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 99
  286 11 5 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 286 (accept_3_3 53 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 286 (accept_3_3 50 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 286 (accept_3_3 47 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 286 (Polychromatic418967fa.accept_25_21_24_11_1_12466 46 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 99 286 11 4 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 286 (accept_3_3 41 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 286 (Polychromatic418967fa.accept_21_18_15_13_1_4130 39 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 286 (accept_3_3 38 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 286 (accept_3_3 35 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 286 (Polychromatic418967fa.accept_19_15_4_1_1_4060 34 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 99 286 11 3 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 99 286 (accept_3_3 32 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 286 (accept_3_3 29 99 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 286
  (Polychromatic418967fa.accept_21_7_15_13_1_5606 28 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 99 286 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 286 (accept_3_3 26 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 286 (Polychromatic418967fa.accept_19_5_4_1_1_12396
  24 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 286 (accept_3_3 23
  99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 286 11 2 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 99 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 286 (accept_3_3 20 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 286 (accept_3_3 17 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 286
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 286 (accept_3_3 14 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 286 11 1 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688
  10 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 286 (accept_3_3 8 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 286 (accept_3_3 5 99 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 286 (Polychromatic418967fa.accept_25_4_24_11_1_17538 4 99 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 286
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 286 (accept_3_3 2 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 286 (allA_of_3_1 98 98 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 286
  (allA_succ_of_accept 96 97 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 96 97 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 286 (accept_3_3 95 97 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 286 (Polychromatic418967fa.accept_17_9_12_14_1_5423 94 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 286 (accept_3_3 92 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 286 (Polychromatic418967fa.accept_19_14_2_1_1_8308 90 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 286 (accept_3_3 89 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 286 (accept_3_3 86 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 85 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 84 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 286 (accept_3_3 83 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 82 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 286 (accept_3_3 80 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 286 (Polychromatic418967fa.accept_24_6_1_22_1_14202 78 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 286 (accept_3_3 77 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 286 (accept_3_3 74 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 73 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 286 (Polychromatic418967fa.accept_19_15_2_1_1_2822 72 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 286 (accept_3_3 71 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 97
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 286 (accept_3_3 68 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 66 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 286 (accept_3_3 65 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 286 (accept_3_3 62 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 286 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 286 (accept_3_3 59 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 58 97
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 286 (accept_3_3 56 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 286 (accept_3_3 53 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 286 (accept_3_3 50 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 286 (Polychromatic418967fa.accept_14_7_13_6_1_1177 49 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 286 (Polychromatic418967fa.accept_25_23_22_11_1_17537 48 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 286 (accept_3_3 47 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 286 (Polychromatic418967fa.accept_19_8_2_1_1_4053 46 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 286 (accept_3_3 44 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 286 (Polychromatic418967fa.accept_29_13_10_25_1_17536 42 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 286 (accept_3_3 41 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 286 (accept_3_3 38 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 286 (accept_3_3 35 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 286 (Polychromatic418967fa.accept_19_15_2_1_1_2822 34 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 286 (accept_3_3 32 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 286 (Polychromatic418967fa.accept_23_7_5_10_1_9675 30 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 286 (accept_3_3 29 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 286 (accept_3_3 26 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 286 (accept_3_3 23 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 286 (accept_3_3 20 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 286 (Polychromatic418967fa.accept_19_18_2_1_1_5375 18 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 286 (accept_3_3 17 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 286 (accept_3_3 14 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 286 (accept_3_3 11 97 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 97
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 286 (accept_3_3 8 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 97 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 286 (accept_3_3 5 97 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 97 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 286 (accept_3_3 2 97 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 1
  97 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 286
  (allA_succ_of_accept 95 96 286 (accept_3_3 95 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  286 2 47 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 286 2 46 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 286 2 45 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 286 (accept_3_3 89 96 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 286 2 44 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 286
  (Polychromatic418967fa.accept_18_15_6_16_1_4730 87 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 286 2 43 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 286 2 42 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 286 (accept_3_3 83 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 286 2 41 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81
  96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 286 2 40 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 286
  (Polychromatic418967fa.accept_25_4_21_11_1_17535 79 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 96 286 2 39 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 96 286 (accept_3_3 77 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 286 2 38 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 96 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 286 2 37 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 286 2 36 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 96 286 (accept_3_3 71 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 286 2 35 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 96 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 69 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 286 2 34 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 286 2 33 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 286 (accept_3_3 65 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 286 2 32 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 286 2 31 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 286
  (Polychromatic418967fa.accept_20_1_16_6_1_4715 61 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 286 2 30 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 286 (accept_3_3 59 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 286 2 29 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 286 2 28 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 286 2 27 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 286 (accept_3_3 53 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 286 2 26 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 96 286 (Polychromatic418967fa.accept_18_15_6_16_1_4730 51 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 286 2 25 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 286 2 24 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 286 (accept_3_3 47 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 286 2 23 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 96 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 45 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 286 2 22 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 286 2 21 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 286 (accept_3_3 41 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 286 2 20 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 286 2 19 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 286 2 18 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 286 (accept_3_3 35 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 286 2 17 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 96 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 286 2 16 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 286 2 15 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 286 (accept_3_3 29 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 286 2 14 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 286 2 13 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 286 2 12 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 286 (accept_3_3 23 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 286 2 11 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 96 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 286 2 10 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 286 2 9 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 286 (accept_3_3 17 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96
  286 2 8 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  96 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 286 2 7 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 96 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 286 2 6 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 286 (accept_3_3 11 96 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 286 2 5 48 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 96 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 286 2 4 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 286 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 96 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 286 2 3 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 286 (accept_3_3 5 96 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 286 2 2 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 286 2 1 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 286
  (allA_of_3_1 95 95 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 286 (allA_succ_of_accept 93 94 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 94 286 2 46 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 94 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 286 2 45 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 286 (accept_3_3 89 94 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 286 2 44 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 94 286 2 43 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 94 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 94 286 2 42 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 94 286 (accept_3_3 83 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 94 286 2 41 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 94 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 286 2 40 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 286 2 39 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 286 (accept_3_3 77 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 286 2 38 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 286 2 37 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 286 2 36 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 286 (accept_3_3 71 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 286 2 35 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 286 2 34 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 286 2 33 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 286 (accept_3_3 65 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 286 2 32 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 286 2 31 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 61 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 286 2 30 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 286 (accept_3_3 59 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 286 2 29 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 286 2 28 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 286 2 27 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 286 (accept_3_3 53 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 286 2 26 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 286 2 25 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 286
  (Polychromatic418967fa.accept_19_11_18_1_1_4048 49 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 286 2 24 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 286 (accept_3_3 47 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 286 2 23 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 286 2 22 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 286 2 21 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 286 (accept_3_3 41 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 286 2 20 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 286 2 19 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 286 2 18 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 286 (accept_3_3 35 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 286 2 17 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 286 2 16 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 286 2 15 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 286 (accept_3_3 29 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 286 2 14 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 286 2 13 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 286 2 12 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 286 (accept_3_3 23 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 286 2 11 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 286 2 10 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 286 2 9 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 286 (accept_3_3 17 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  286 2 8 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 286 2 7 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 286 (Polychromatic418967fa.accept_19_13_18_1_1_8215 13 94 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 286 2 6 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 286 (accept_3_3 11 94 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 286 2 5 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 286 2 4 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 286 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 94 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 286 2 3 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 286 (accept_3_3 5 94 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 286 2 2 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 286 2 1 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 286
  (allA_succ_of_accept 92 93 286 (accept_3_3 92 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 286 (accept_3_3 89 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 286 (accept_3_3 86 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 286 (Polychromatic418967fa.accept_17_16_8_14_1_6757 84 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 286 (accept_3_3 83 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 93 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 286 (accept_3_3 80 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 286 (accept_3_3 77 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 286 (accept_3_3 74 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 286 (Polychromatic418967fa.accept_19_15_17_1_1_8225 72 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 286 (accept_3_3 71 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 286 (Polychromatic418967fa.accept_21_7_9_13_1_5612 70 93
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 286 (accept_3_3 68 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 286 (accept_3_3 65 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 286 (accept_3_3 62 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 286 (accept_3_3 59 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 286 (accept_3_3 56 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 286 (accept_3_3 53 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 286 (accept_3_3 50 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 286 (accept_3_3 47 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 286 (accept_3_3 44 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 286 (accept_3_3 41 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 286 (accept_3_3 38 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 286 (accept_3_3 35 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 286 (accept_3_3 32 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 286 (accept_3_3 29 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 286 (accept_3_3 26 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 286 (accept_3_3 23 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 286 (accept_3_3 20 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 286 (accept_3_3 17 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 286 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 286 (accept_3_3 14 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 286 (Polychromatic418967fa.accept_21_12_9_13_1_4091 12 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 286 (accept_3_3 11 93 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 93 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 286
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 286 (accept_3_3 8 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 286 (accept_3_3 5 93 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 286 (accept_3_3 2 93 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 286
  (allA_of_3_1 92 92 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 286 (allA_succ_of_accept 90 91 286
  (Polychromatic418967fa.accept_19_14_15_1_1_6806 90 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 286 (accept_3_3 89 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 286 (accept_3_3 86 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 286 (accept_3_3 83 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 286 (accept_3_3 80 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 286 (Polychromatic418967fa.accept_18_7_1_16_1_578 79 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 91 286 13 6 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 91 286 (accept_3_3 77 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 286 (accept_3_3 74 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 286 (accept_3_3 71 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 286 (Polychromatic418967fa.accept_25_20_16_11_1_17534 70 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 286 (accept_3_3 68 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 91 286 13 5 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 91 286 (Polychromatic418967fa.accept_12_4_7_10_1_563
  64 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 286 (accept_3_3 62 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 286 (accept_3_3 59 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 286 (accept_3_3 56 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 286 (Polychromatic418967fa.accept_17_3_6_14_1_4312 54 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 286 (accept_3_3 53 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 91 286 13 4 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 91 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 286 (accept_3_3 50 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 286 (accept_3_3 47 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 286 (accept_3_3 44 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 286 (Polychromatic418967fa.accept_14_1_7_6_1_3604 43 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 286 (accept_3_3 41 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 91 286 13 3 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 91 286 (accept_3_3 38 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 286 (accept_3_3 35 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 286
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 286 (accept_3_3 32 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 30
  91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 286 (accept_3_3 29 91
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 286
  (Polychromatic418967fa.accept_12_4_7_10_1_563 28 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 91 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 91 286 13 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 286 (accept_3_3 23 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 286 (accept_3_3 20 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 286 (Polychromatic418967fa.accept_16_3_11_14_1_446 19 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 286
  (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 286 (accept_3_3 17 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 286 (accept_3_3 14 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91 286 13 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 91 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 286 (accept_3_3 11 91 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 91
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 286 (accept_3_3 8 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  286 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 91 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 286 (accept_3_3 5 91 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 286 (accept_3_3 2 91 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 286
  (allA_succ_of_accept 89 90 286 (accept_3_3 89 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  286 2 44 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 87 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 286 2 43 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 90 286 (Polychromatic418967fa.accept_16_5_10_14_1_5074 85 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 286 2 42 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 286 (accept_3_3 83 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 286 2 41 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 286 2 40 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 286 (Polychromatic418967fa.accept_16_15_10_14_1_2872 79 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 286 2 39 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 286 (accept_3_3 77 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 286 2 38 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 75 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 286 2 37 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 286 (Polychromatic418967fa.accept_23_4_21_10_1_14421 73 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 286 2 36 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 286 (accept_3_3 71 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 286 2 35 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 286 2 34 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 286 (Polychromatic418967fa.accept_19_10_14_1_1_8296 67 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 286 2 33 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 286 (accept_3_3 65 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 286 2 32 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 286 2 31 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 286 (Polychromatic418967fa.accept_16_13_10_14_1_2871 61 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 286 2 30 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 286 (accept_3_3 59 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 286 2 29 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 286 2 28 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 55 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 286 2 27 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 286 (accept_3_3 53 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 286 2 26 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 286 2 25 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 286 (Polychromatic418967fa.accept_20_9_10_6_1_16252 49 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 286 2 24 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 286 (accept_3_3 47 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 286 2 23 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 286 2 22 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 286 (Polychromatic418967fa.accept_17_9_5_14_1_4277 43 90 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 286 2 21 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 286 (accept_3_3 41 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 286 2 20 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  39 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 286 2 19 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 286
  (Polychromatic418967fa.accept_16_5_10_14_1_5074 37 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 286 2 18 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 286 (accept_3_3 35 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 286 2 17 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 90 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 286 2 16 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 286
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 90 286 2 15 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 90 286 (accept_3_3 29 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 286 2 14 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 90 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 286 2 13 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 286
  (Polychromatic418967fa.accept_19_6_14_1_1_2752 25 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 286 2 12 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 286 (accept_3_3 23 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 286 2 11 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 90 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 286 2 10 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 286
  (Polychromatic418967fa.accept_17_2_5_14_1_2068 19 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 286 2 9 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 286 (accept_3_3 17 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90
  286 2 8 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  90 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 90 286 2 7 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 90 286 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 90 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 286 2 6 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 286 (accept_3_3 11 90 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 286 2 5 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 286 2 4 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 90 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 286 2 3 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 286 (accept_3_3 5 90 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 286 2 2 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 286 2 1 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 286 (Polychromatic418967fa.accept_25_1_15_11_1_6999
  1 90 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 286
  (allA_of_3_1 89 89 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 286 (allA_succ_of_accept 87 88 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 286 2 43 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 88 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 85 88 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 286 2 42 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 286 (accept_3_3 83 88 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 286 2 41 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 286 (Polychromatic418967fa.accept_19_5_12_1_1_2817
  81 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 286 2 40 44 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 286 2 39 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 88 286 11 7 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 88 286 2 38 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 88 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 88 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 286 2 37 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 286 2 36 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 88 286 (accept_3_3 71 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 88 286 2 35 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 88 286 (Polychromatic418967fa.accept_21_6_4_13_1_8740 69 88 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 286 2 34 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 286 22 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 88 286 (accept_3_3 65 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88
  286 2 32 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  63 88 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 286 2 31 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 88 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 286 2 30 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 286 (accept_3_3 59 88 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 286 2 29 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 286
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 286 2 28 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 88 286 11 5 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 88 286 2 27 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 88 286 (accept_3_3 53 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 286 2 26 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 88 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 88 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 286 2 25 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 286 2 24 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 88 286 (accept_3_3 47 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 286 2 23 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 88 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 88 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 286 22 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 43
  88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 286 2 21 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 286 (accept_3_3 41
  88 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 286 2 20 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 286
  (Polychromatic418967fa.accept_21_18_4_13_1_5602 39 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 88 286 2 19 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 88 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 286 2 18 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 286 (accept_3_3 35 88 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 286 2 17 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 88 286 11 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 88 286 2 16 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 286 2 15 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 88 286 (accept_3_3 29 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 286 2 14 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 88 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 88 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 286 2 13 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 286 2 12 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 88 286 (accept_3_3 23 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 88 286 22 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 88 286 (Polychromatic418967fa.accept_19_2_12_1_1_2815 21 88 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 286 2 10 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19
  88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 286 2 9 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 286 (accept_3_3 17
  88 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 286 2 8 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 286
  (Polychromatic418967fa.accept_17_15_3_14_1_4230 15 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 88 286 2 7 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 88 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 286 2 6 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 88 286 11 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 88 286 2 5 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 286 2 4 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 286 2 3 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 286 (accept_3_3 5 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 286
  2 2 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 286 2 1 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 88 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 286
  (allA_succ_of_accept 86 87 286 (accept_3_3 86 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 286 (accept_3_3 83 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 286 (accept_3_3 80 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 78 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 286 (accept_3_3 77 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 286 (accept_3_3 74 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 286 (accept_3_3 71 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 286 (Polychromatic418967fa.accept_25_20_12_11_1_15911 70 87 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 286 (accept_3_3 68 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 286 (accept_3_3 65 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 286
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 286 (accept_3_3 62 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 286 (accept_3_3 59 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 286 (accept_3_3 56 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 286 (accept_3_3 53 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 286 (accept_3_3 50 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 286 (accept_3_3 47 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 286 (accept_3_3 44 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 286 (accept_3_3 41 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 286 (accept_3_3 38 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 286 (accept_3_3 35 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 87
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 286 (accept_3_3 32 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 286 (accept_3_3 29 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 286
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 27 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 286 (accept_3_3 26 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 286 (accept_3_3 23 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 87 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 286 (accept_3_3 20 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 286 (accept_3_3 17 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 286
  (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 286 (accept_3_3 14 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 286 (accept_3_3 11 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 286 (accept_3_3 8 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 286 (accept_3_3 5 87 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  87 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 286 (accept_3_3 2 87 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 286
  (allA_of_3_1 86 86 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 286 (allA_succ_of_accept 84 85 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 286 (accept_3_3 83 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 286 (accept_3_3 80 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 286 (accept_3_3 77 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 286 (accept_3_3 74 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 286 (accept_3_3 71 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 286 (Polychromatic418967fa.accept_20_10_5_6_1_12032 70 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 286 (accept_3_3 68 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 286 (accept_3_3 65 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 286 (accept_3_3 62 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 286 (accept_3_3 59 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 286 (accept_3_3 56 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 286 (accept_3_3 53 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 286 (accept_3_3 50 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 286 (accept_3_3 47 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 286 (accept_3_3 44 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 286 (accept_3_3 41 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 286 (accept_3_3 38 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 286 (accept_3_3 35 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 286 (accept_3_3 32 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 286 (accept_3_3 29 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 286 (accept_3_3 26 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 25 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 286 (accept_3_3 23 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 286 (accept_3_3 20 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 286
  (Polychromatic418967fa.accept_25_18_10_11_1_17533 18 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 85 286 (accept_3_3 17 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 85 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 286 (accept_3_3 14 85 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 286
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 286 (accept_3_3 11 85 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 286 (accept_3_3 8 85 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 286 (accept_3_3 5 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  286 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 286 (accept_3_3 2 85 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 286
  (allA_succ_of_accept 83 84 286 (accept_3_3 83 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  286 2 41 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 286 2 40 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 79 84 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 286 2 39 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 286 (accept_3_3 77 84 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 286 2 38 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 286 2 37 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 286 2 36 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 286 (accept_3_3 71 84 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 286 2 35 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 286 2 34 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 286 2 33 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 286 (accept_3_3 65 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 286 2 32 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 84 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 84 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 286 2 31 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 286
  (Polychromatic418967fa.accept_27_7_3_16_1_17532 61 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 286 2 30 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 286 (accept_3_3 59 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 286 2 29 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 84 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 57 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 286 2 28 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 286 2 27 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 286 (accept_3_3 53 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 286 2 26 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 84 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 286 2 25 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 286 2 24 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 286 (accept_3_3 47 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 286 2 23 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 286 2 22 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 286
  (Polychromatic418967fa.accept_31_12_22_7_1_17531 43 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 84 286 2 21 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 84 286 (accept_3_3 41 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 286 2 20 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 84 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 286 2 19 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 286 2 18 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 286 (accept_3_3 35 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 286 2 17 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 84 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 286 2 16 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 286 2 15 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 286 (accept_3_3 29 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 286 2 14 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 27 84 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 286 2 13 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 286 2 12 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 286 (accept_3_3 23 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 286 2 11 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 84 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 286 2 10 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 286 2 9 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 286 (accept_3_3 17 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  286 2 8 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 286 2 7 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 84 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 286 2 6 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 286 (accept_3_3 11 84 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 286 2 5 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 84 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 286 2 4 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 84 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 286 2 3 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 286 (accept_3_3 5 84 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 286 2 2 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 286 (Polychromatic418967fa.accept_29_3_26_25_1_17530 3 84 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 286 2 1 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 286 (allA_of_3_1
  83 83 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 286 (allA_succ_of_accept 81 82 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 286 2 40 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 286 (Polychromatic418967fa.accept_19_3_6_1_1_4064 79 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 286 2 39 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 286 (accept_3_3 77 82 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 286 2 38 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 75
  82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 286 2 37 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 73 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 286 2 36 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 286 (accept_3_3 71 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 286 2 35 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 286 2 34 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 286 2 33 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 286 (accept_3_3 65 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 286 2 32 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 286 (Polychromatic418967fa.accept_25_13_7_11_1_17529 63 82 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 286 2 31 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 286 2 30 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 286 (accept_3_3 59 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 286 2 29 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 286 2 28 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 55 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 286 2 27 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 286 (accept_3_3 53 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 286 2 26 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 286 2 25 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 286 2 24 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 286 (accept_3_3 47 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 286 2 23 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 286 (Polychromatic418967fa.accept_19_7_6_1_1_796 45 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 286 2 22 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 286 2 21 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 286 (accept_3_3 41 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 286 2 20 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 286 2 19 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 286 2 18 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 286 (accept_3_3 35 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 286 2 17 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 286 2 16 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 286 2 15 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 286 (accept_3_3 29 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 286 2 14 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 82 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 286 2 13 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 286 2 12 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 286 (accept_3_3 23 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 286 2 11 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 286 2 10 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 286 2 9 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 286 (accept_3_3 17 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  286 2 8 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 286 2 7 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 286 2 6 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 286 (accept_3_3 11 82 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 286 2 5 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 286
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 82 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 286 2 4 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 286 (Polychromatic418967fa.accept_19_7_6_1_1_796 7 82 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 286 2 3 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 286 (accept_3_3 5 82 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 286 2 2 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 286 2 1 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 286
  (allA_succ_of_accept 80 81 286 (accept_3_3 80 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 78 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 286 (accept_3_3 77 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 286 (Polychromatic418967fa.accept_20_16_1_6_1_6196 76 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 286 (accept_3_3 74 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 286 (accept_3_3 71 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 69 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 286 (accept_3_3 68 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 286 (accept_3_3 65 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 286 (Polychromatic418967fa.accept_24_16_9_22_1_14220 64 81 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 286 (accept_3_3 62 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 286 (Polychromatic418967fa.accept_19_3_5_1_1_6811 60 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 286 (accept_3_3 59 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 286
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 286 (accept_3_3 56 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 286 (accept_3_3 53 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 286 (accept_3_3 50 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 286 (accept_3_3 47 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 286 (Polychromatic418967fa.accept_21_4_18_13_1_10435 46 81 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 286 (accept_3_3 44 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 286 (accept_3_3 41 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 286 (accept_3_3 38 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 286 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 286 (accept_3_3 35 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 286 (Polychromatic418967fa.accept_19_15_5_1_1_5360 34 81
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 286 (accept_3_3 32 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 286 (accept_3_3 29 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 286 (Polychromatic418967fa.accept_19_9_5_1_1_2766 28 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 286 (accept_3_3 26 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 286 (accept_3_3 23 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 286
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 21 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 286 (accept_3_3 20 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 286 (accept_3_3 17 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 286 (accept_3_3 14 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 286 (accept_3_3 11 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 286 (accept_3_3 8 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 286 (accept_3_3 5 81 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 286 (Polychromatic418967fa.accept_16_4_1_14_1_3908 4 81 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 286 (accept_3_3 2 81 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 286 (allA_of_3_1 80
  80 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 286 (allA_succ_of_accept 78 79 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 286 (accept_3_3 77 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 286 (accept_3_3 74 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 286 (accept_3_3 71 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 286 (Polychromatic418967fa.accept_20_10_19_6_1_13499 70 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 286 (accept_3_3 68 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 286 (accept_3_3 65 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 286 (accept_3_3 62 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 286 (accept_3_3 59 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 286 (Polychromatic418967fa.accept_16_10_15_14_1_1086 58 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 286 (accept_3_3 56 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 286
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 54 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 286 (accept_3_3 53 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 286 (accept_3_3 50 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 286 (accept_3_3 47 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 286 (accept_3_3 44 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 286 (accept_3_3 41 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 286 (accept_3_3 38 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 286 (accept_3_3 35 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 286 (accept_3_3 32 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 286
  (Polychromatic418967fa.accept_19_11_3_1_1_2799 30 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 286 (accept_3_3 29 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 286 (accept_3_3 26 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 286 (accept_3_3 23 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 286 (accept_3_3 20 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 286 (accept_3_3 17 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 286 (accept_3_3 14 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 286 (accept_3_3 11 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 286 (accept_3_3 8 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 286 (Polychromatic418967fa.accept_16_7_15_14_1_2889 7 79 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 286
  (Polychromatic418967fa.accept_19_6_3_1_1_2824 6 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 286 (accept_3_3 5 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 286 (accept_3_3 2 79 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 286
  (allA_succ_of_accept 77 78 286 (accept_3_3 77 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  286 2 38 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 286 2 37 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 78 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 286 2 36 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 286 (accept_3_3 71 78 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 286 2 35 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 286 2 34 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 286 2 33 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 78 286 13 5 6 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 78 286 2 32 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 286 2 31 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 286 2 30 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 286 (accept_3_3 59 78 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 286 2 29 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57
  78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 286 2 28 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 286 2 27 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 286 (accept_3_3 53 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 286 26 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 286 2 25 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 49
  78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 286 2 24 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 286 (accept_3_3 47
  78 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 286 2 23 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 286 2 22 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 286 2 21 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 286 (accept_3_3 41 78 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 286 2 20 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 286 13 3 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 286 2 19 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 286 2 18 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 286 (accept_3_3 35 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 286 2 17 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 286 2 16 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 286 2 15 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 286 (accept_3_3 29 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 286 2 14 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 286 26 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 286 (Polychromatic418967fa.accept_19_6_2_1_1_4051
  25 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 286 2 12 39 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 286
  (accept_3_3 23 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 286 2 11 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 286 2 10 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 286 2 9 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 286 (accept_3_3 17 78 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 286 2 8 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  15 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 286 2 7 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 78 286 13 1 6 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 286 2 6 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 286 (accept_3_3 11
  78 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 286 2 5 39 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 286 2 4 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 78 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 286 2 3 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 286 (accept_3_3 5 78 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 286 2 2 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 286 2 1 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 286 (allA_of_3_1 77 77
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 286 (allA_succ_of_accept 75 76 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 286 2 37 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 286 2 36 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 286 (accept_3_3 71 76 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 286 2 35 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69
  76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 286 2 34 38 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 286 2 33 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 286 (accept_3_3 65 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 286 2 32 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 76 286 (Polychromatic418967fa.accept_23_17_7_10_1_17528 63 76 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 286 2 31 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 76 286 2 30 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 76 286 (accept_3_3 59 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 76 286 2 29 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 76 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 286 2 28 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 286 2 27 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 76 286 (accept_3_3 53 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 286 2 26 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 76 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 286 2 25 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 286 2 24 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 76 286 (accept_3_3 47 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 76 286 2 23 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 76 286 (Polychromatic418967fa.accept_17_11_8_14_1_8084 45 76 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 76 286 2 22 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 76 286 2 21 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 76 286 (accept_3_3 41 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 76 286 2 20 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 76 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 286 2 19 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 286 2 18 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 76 286 (accept_3_3 35 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 76 286 2 17 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 76 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 286 2 16 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 286 2 15 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 286 (accept_3_3 29 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 286 2 14 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 76 286 (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 286 2 13 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 286 2 12 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 286 (accept_3_3 23 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 76 286 2 11 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 286 2 10 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 286 2 9 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 286 (accept_3_3 17 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  286 2 8 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 286 2 7 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 76 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 76 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 286 2 6 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 286 (accept_3_3 11 76 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 286 2 5 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 286
  (Polychromatic418967fa.accept_25_9_1_11_1_15936 9 76 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 286 2 4 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 286 2 3 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 286 (accept_3_3 5 76 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 286 2 2 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 286 2 1 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 286 (allA_succ_of_accept
  74 75 286 (accept_3_3 74 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 286 (Polychromatic418967fa.accept_17_4_7_14_1_10583 72 75 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 286 (accept_3_3 71 75 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 286 (Polychromatic418967fa.accept_19_13_18_1_1_8215 70 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 286 (accept_3_3 68 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 66 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 286 (accept_3_3 65 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 286
  (Polychromatic418967fa.accept_19_6_18_1_1_17527 63 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 286 (accept_3_3 62 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 286 (accept_3_3 59 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 286 (accept_3_3 56 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 286 (accept_3_3 53 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 286 (Polychromatic418967fa.accept_19_14_18_1_1_12442 52 75 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 286 (accept_3_3 50 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 286 (Polychromatic418967fa.accept_28_20_19_6_1_17526 48 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 286 (accept_3_3 47 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 75 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 286 (accept_3_3 44 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 286 (accept_3_3 41 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 286 (accept_3_3 38 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 286 (accept_3_3 35 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 286 (accept_3_3 32 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 286 (accept_3_3 29 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 286
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 286 (accept_3_3 26 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 286 (accept_3_3 23 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 286 (accept_3_3 20 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 286 (accept_3_3 17 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 286 (Polychromatic418967fa.accept_23_16_6_10_1_7930 16 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 286 (accept_3_3 14 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 286 (Polychromatic418967fa.accept_19_12_18_1_1_12336 12 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 286 (accept_3_3 11 75 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 286 (accept_3_3 8 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 286 (accept_3_3 5 75 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 286 (Polychromatic418967fa.accept_16_3_11_14_1_446
  3 75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 286 (accept_3_3 2 75
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  75 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 286 (allA_of_3_1 74 74
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 286 (allA_succ_of_accept 72 73 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 286 (accept_3_3 71 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 286 (accept_3_3 68 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 286 (accept_3_3 65 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 286 (accept_3_3 62 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 286 (Polychromatic418967fa.accept_17_10_5_14_1_4203 61 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 286 (accept_3_3 59 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 286 (accept_3_3 56 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 286
  (Polychromatic418967fa.accept_24_6_1_22_1_14202 54 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 286 (accept_3_3 53 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 286 (accept_3_3 50 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 286 (accept_3_3 47 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 286 (accept_3_3 44 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 286 (accept_3_3 41 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 286 (accept_3_3 38 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 286
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 286 (accept_3_3 35 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 286 (Polychromatic418967fa.accept_19_15_16_1_1_11087 34 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 286 (accept_3_3 32 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 286 (accept_3_3 29 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 286 (accept_3_3 26 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 286 (accept_3_3 23 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 286 (accept_3_3 20 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 286 (accept_3_3 17 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 286 (accept_3_3 14 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 286 (accept_3_3 11 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 286 (accept_3_3 8 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 286 (accept_3_3 5 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 286 (accept_3_3 2 73 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 286 (Polychromatic418967fa.accept_21_1_10_13_1_5623 1 73 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 286 (allA_succ_of_accept 71
  72 286 (accept_3_3 71 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 286 2 35 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 286
  (Polychromatic418967fa.accept_17_1_4_14_1_8058 69 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 286 2 34 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 72 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 286 2 33 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 286 (accept_3_3 65 72 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 286 2 32 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 286 (Polychromatic418967fa.accept_23_17_3_10_1_4426
  63 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 286 2 31 36 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 286 2 30 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 72 286 (accept_3_3 59 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 286 2 29 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 72 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 286 2 28 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 286
  (Polychromatic418967fa.accept_19_17_15_1_1_8300 55 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 286 2 27 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 286 (accept_3_3 53 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 286 2 26 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 72 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 286 2 25 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 286
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 286 2 24 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 286 (accept_3_3 47 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 286 2 23 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 72 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 286 2 22 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 286 2 21 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 286 (accept_3_3 41 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 286 2 20 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 286 2 19 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 286
  (Polychromatic418967fa.accept_20_17_12_6_1_6171 37 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 286 2 18 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 286 (accept_3_3 35 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 286 2 17 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 72 286 (Polychromatic418967fa.accept_19_14_15_1_1_6806 33 72 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 286 2 16 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 286 2 15 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 286 (accept_3_3 29 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 286 2 14 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 286 (Polychromatic418967fa.accept_19_8_15_1_1_3979 27 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 286 2 13 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 286 2 12 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 286 (accept_3_3 23 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 286 2 11 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 72 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 286 2 10 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 286
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 286 2 9 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 286 (accept_3_3 17 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  286 2 8 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 286 2 7 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 72 286 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 72 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 286 2 6 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 286 (accept_3_3 11 72 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 286 2 5 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 72 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 286 2 4 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 286 (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 72 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 286 2 3 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 286 (accept_3_3 5 72 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 286 2 2 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 286 2 1 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 286 (allA_of_3_1 71 71 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 286 (allA_succ_of_accept 69 70 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 69 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 286 2 34 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 286 2 33 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 286 (accept_3_3 65 70 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 286 2 32 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 286 (Polychromatic418967fa.accept_28_7_14_6_1_17525
  63 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 286 2 31 35 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 286
  (Polychromatic418967fa.accept_21_19_7_13_1_7189 61 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 286 2 30 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 70 286 (accept_3_3 59 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 70 286 2 29 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 70 286 (Polychromatic418967fa.accept_21_15_7_13_1_14725 57 70 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 286 2 28 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 286
  (Polychromatic418967fa.accept_20_15_10_6_1_6169 55 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 286 2 27 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 286 (accept_3_3 53 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 286 2 26 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 286 2 25 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 286
  (Polychromatic418967fa.accept_20_9_10_6_1_16252 49 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 286 2 24 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 70 286 (accept_3_3 47 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 70 286 2 23 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 70 286 (Polychromatic418967fa.accept_19_7_13_1_1_6804 45 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 286 2 22 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 286
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 286 2 21 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 286 (accept_3_3 41 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 286 2 20 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 286 (Polychromatic418967fa.accept_15_9_10_1_1_1062 39 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 286 2 19 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 286
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 286 2 18 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 70 286 (accept_3_3 35 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 286 2 17 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 286 (Polychromatic418967fa.accept_17_16_2_14_1_6715 33 70 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 286 2 16 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 286
  (Polychromatic418967fa.accept_19_12_13_1_1_2779 31 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 286 2 15 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 286 (accept_3_3 29 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 286 2 14 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 70 286 (Polychromatic418967fa.accept_19_8_13_1_1_8221 27 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 286 2 13 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 286
  (Polychromatic418967fa.accept_20_5_10_6_1_6166 25 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 286 2 12 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 70 286 (accept_3_3 23 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 286 2 11 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 70 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 286 2 10 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 286
  (Polychromatic418967fa.accept_20_19_10_6_1_14774 19 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 70 286 2 9 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 70 286 (accept_3_3 17 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 70 286 2 8 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 70 286 (Polychromatic418967fa.accept_20_15_10_6_1_6169 15 70 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 286 2 7 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862
  13 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 286 2 6 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 286 (accept_3_3 11
  70 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 286 2 5 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 286 2 4 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 70 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 286 2 3 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 286 (accept_3_3 5 70 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 286 2 2 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 286 (Polychromatic418967fa.accept_17_3_2_14_1_6714 3 70 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 286 2 1 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 286 (Polychromatic418967fa.accept_28_1_14_6_1_17524
  1 70 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 286 (allA_succ_of_accept 68 69
  286 (accept_3_3 68 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 286 (accept_3_3 65 69 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 286 (accept_3_3 62 69
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 286
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 69 286 (accept_3_3 59 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  69 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 286 (accept_3_3 56 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 286 (accept_3_3 53 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 286 (accept_3_3 50 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 286 (accept_3_3 47 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 286 (accept_3_3 44 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 286 (accept_3_3 41 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 286 (accept_3_3 38 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 286 (accept_3_3 35 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 286 (accept_3_3 32 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 286 (accept_3_3 29 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 286 (accept_3_3 26 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 286
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 286 (accept_3_3 23 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 286 (accept_3_3 20 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 286 (accept_3_3 17 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 286 (Polychromatic418967fa.accept_21_16_6_13_1_10430 16 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 286 (accept_3_3 14 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 286 (accept_3_3 11 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 286 (accept_3_3 8 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 286 (accept_3_3 5 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 286 (accept_3_3 2 69 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 286 (allA_of_3_1 68 68 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 286 (allA_succ_of_accept 66 67 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 286 (accept_3_3 65 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 286 (accept_3_3 62 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 286 (accept_3_3 59 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 286 (accept_3_3 56 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 286 (accept_3_3 53 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 286 (accept_3_3 50 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 286 (accept_3_3 47 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 286 (accept_3_3 44 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 286 (accept_3_3 41 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 286 (accept_3_3 38 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 286
  (Polychromatic418967fa.accept_15_6_7_1_1_93 36 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 286 (accept_3_3 35 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 286 (Polychromatic418967fa.accept_23_11_21_10_1_17523 34 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 286 (accept_3_3 32 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 286 (accept_3_3 29 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 286 (accept_3_3 26 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 286 (accept_3_3 23 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 286 (Polychromatic418967fa.accept_19_3_10_1_1_12449 22 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 286 (accept_3_3 20 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 286
  (Polychromatic418967fa.accept_21_18_4_13_1_5602 18 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 286 (accept_3_3 17 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 286 (accept_3_3 14 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 286 (accept_3_3 11 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 286 (accept_3_3 8 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 286 (Polychromatic418967fa.accept_19_7_10_1_1_5382 7 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 286 (accept_3_3 5 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 286 (accept_3_3 2 67 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 286 (allA_succ_of_accept 65 66
  286 (accept_3_3 65 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 286 2 32 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 286 2 31 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 286 (Polychromatic418967fa.accept_28_5_10_6_1_17522 61 66 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 286 2 30 33 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 286 (accept_3_3 59 66 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 286 2 29 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 286 2 28 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 66 286 11 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 66 286 2 27 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 66 286 (accept_3_3 53 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 286 2 26 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 66 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 286 2 25 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 286 2 24 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 286 (accept_3_3 47 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 286 2 23 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 66 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 286 22 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 286 (Polychromatic418967fa.accept_19_5_9_1_1_5393
  43 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 286 2 21 33 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 286
  (accept_3_3 41 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 286 2 20 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 286 2 19 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 286 2 18 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 286 (accept_3_3 35 66 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 286 2 17 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 286 11 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 286 2 16 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 286 2 15 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 286 (accept_3_3 29 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 286 2 14 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 286 2 13 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 286 2 12 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 286 (accept_3_3 23 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 286 22 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 286 2 10 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 286 2 9 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 286 (accept_3_3 17
  66 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 286 2 8 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 286 2 7 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 286 2 6 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 286 11 1 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 286 2 5 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 286 2 4 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 286 2 3 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 286 (accept_3_3 5 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 286
  2 2 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 286 2 1 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 286 (allA_of_3_1 65 65 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 286 (allA_succ_of_accept 63 64 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 286 2 31 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 64 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 286 2 30 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 286 (accept_3_3 59 64 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 286 2 29 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57
  64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 286 2 28 32 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 286 2 27 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 286 (accept_3_3 53 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 64 286 2 26 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 64 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 286 2 25 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 286 2 24 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 64 286 (accept_3_3 47 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 64 286 2 23 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 64 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 286 2 22 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 286 2 21 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 64 286 (accept_3_3 41 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 64 286 2 20 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 64 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 286 2 19 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 286 2 18 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 64 286 (accept_3_3 35 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 64 286 2 17 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 64 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 286 2 16 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 286 2 15 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 64 286 (accept_3_3 29 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 64 286 2 14 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 64 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 286 2 13 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 286 2 12 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 64 286 (accept_3_3 23 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 64 286 2 11 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 286 2 10 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 286 2 9 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 286 (accept_3_3 17 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  286 2 8 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 286 2 7 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 64 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 286 2 6 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 286 (accept_3_3 11 64 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 286 2 5 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 286 2 4 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 64 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 286 2 3 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 286 (accept_3_3 5 64 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 286 2 2 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 64 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 286 2 1 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 286 (allA_succ_of_accept 62 63 286
  (accept_3_3 62 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 286 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 63 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 286 (accept_3_3 59 63 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 286 (accept_3_3 56 63
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  55 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 286 (accept_3_3 53 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 286 (Polychromatic418967fa.accept_16_4_15_14_1_5056 52 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 286 (accept_3_3 50 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 286 (accept_3_3 47 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 286 (Polychromatic418967fa.accept_27_19_9_16_1_17521 46 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 286 (accept_3_3 44 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 286 (accept_3_3 41 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 286 (Polychromatic418967fa.accept_19_2_6_1_1_9729 40 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 286 (accept_3_3 38 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 286 (accept_3_3 35 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  63 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 286 (accept_3_3 32 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 286 (accept_3_3 29 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 286 (accept_3_3 26 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 286
  (Polychromatic418967fa.accept_19_5_6_1_1_5366 24 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 286 (accept_3_3 23 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 286 (accept_3_3 20 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 286 (accept_3_3 17 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 286 (Polychromatic418967fa.accept_23_16_17_10_1_17520 16 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 286 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 286 (accept_3_3 14 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 286 (accept_3_3 11 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 286 (Polychromatic418967fa.accept_16_10_15_14_1_1086 10 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 286 (accept_3_3 8 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 286 (accept_3_3 5 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  286 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 63 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 286 (Polychromatic418967fa.accept_19_3_6_1_1_4064 3 63 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 286 (accept_3_3 2 63 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 286 (allA_of_3_1 62 62 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 286 (allA_succ_of_accept 60 61 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 286 (accept_3_3 59 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 58 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 286 (accept_3_3 56 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 286
  (Polychromatic418967fa.accept_19_16_4_1_1_5376 54 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 286 (accept_3_3 53 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 286 (accept_3_3 50 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 49 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 286
  (Polychromatic418967fa.accept_19_10_4_1_1_4018 48 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 286 (accept_3_3 47 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 286 (accept_3_3 44 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 286 (accept_3_3 41 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 286 (accept_3_3 38 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 286 (accept_3_3 35 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 286 (Polychromatic418967fa.accept_19_15_4_1_1_4060 34 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 286 (accept_3_3 32 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 286
  (Polychromatic418967fa.accept_17_13_10_14_1_4211 30 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 61 286 (accept_3_3 29 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 61 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 286 (accept_3_3 26 61 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 25
  61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 286
  (Polychromatic418967fa.accept_17_7_10_14_1_8022 24 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 286 (accept_3_3 23 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 286 (accept_3_3 20 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 286 (accept_3_3 17 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 286 (accept_3_3 14 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 286 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 286 (accept_3_3 11 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 10 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 286 (accept_3_3 8 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 286
  (Polychromatic418967fa.accept_21_6_19_13_1_7196 6 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 286 (accept_3_3 5 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 286 (accept_3_3 2 61 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 286 (allA_succ_of_accept 59 60 286 (accept_3_3 59 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 286 2 29 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 286 2 28 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 286 2 27 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 60 286 (accept_3_3 53 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 286 2 26 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 60 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 286 2 25 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 286 2 24 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 60 286 (accept_3_3 47 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 60 286 2 23 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 60 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 286 2 22 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 286
  (Polychromatic418967fa.accept_19_5_3_1_1_4055 43 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 286 2 21 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 286 (accept_3_3 41 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 286 2 20 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 60 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 286 2 19 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 286 2 18 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 60 286 (accept_3_3 35 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 286 2 17 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 60 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 286 2 16 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 286 2 15 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 286 (accept_3_3 29 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 286 2 14 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 286 (Polychromatic418967fa.accept_21_6_18_13_1_8767 27 60 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 286 2 13 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 286
  (Polychromatic418967fa.accept_19_6_3_1_1_2824 25 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 286 2 12 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 286 (accept_3_3 23 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 286 2 11 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 286 2 10 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 286 2 9 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 286 (accept_3_3 17 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  286 2 8 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 286 (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 286 2 7 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 60 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 286 2 6 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 286 (accept_3_3 11 60 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 286 2 5 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 286 2 4 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 286 (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 60 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 286 2 3 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 286 (accept_3_3 5 60 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 60 286 2 2 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 286 2 1 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 286 (allA_of_3_1 59 59 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 286 (allA_succ_of_accept 57 58 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 286 2 28 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 286 2 27 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 286 (accept_3_3 53 58 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 286 2 26 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51
  58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 286 2 25 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 286
  (Polychromatic418967fa.accept_21_7_16_13_1_2733 49 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 286 2 24 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 286 (accept_3_3 47 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 286 2 23 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 286 2 22 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 286 2 21 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 286 (accept_3_3 41 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 286 2 20 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 286 2 19 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 286 2 18 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 286 (accept_3_3 35 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 286 2 17 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 286 2 16 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 286 2 15 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 286 (accept_3_3 29 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 286 2 14 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 58 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 286 2 13 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 286 2 12 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 286 (accept_3_3 23 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 286 2 11 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 286 2 10 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 286 2 9 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 286 (accept_3_3 17 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  286 2 8 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 286 2 7 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 58 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 286 2 6 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 286 (accept_3_3 11 58 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 286 2 5 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 286
  (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 58 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 286 2 4 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 58 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 286 2 3 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 286 (accept_3_3 5 58 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 286 2 2 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 286 2 1 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 286 (allA_succ_of_accept 56 57 286
  (accept_3_3 56 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 286 (accept_3_3 53 57 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 52 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 286 (accept_3_3 50 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 286 (Polychromatic418967fa.accept_21_6_15_13_1_13252 48 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 286 (accept_3_3 47 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 286
  (Polychromatic418967fa.accept_23_22_11_10_1_6063 45 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 286 (accept_3_3 44 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 286 (accept_3_3 41 57 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40
  57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 286 (accept_3_3 38 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 286 (accept_3_3 35 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 57
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 286 (accept_3_3 32 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 286 (accept_3_3 29 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 286 (accept_3_3 26 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 286 (accept_3_3 23 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 286
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 286 (accept_3_3 20 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 286 (accept_3_3 17 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 286 (accept_3_3 14 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 286 (accept_3_3 11 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 57 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 286 (accept_3_3 8 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 286 (accept_3_3 5 57 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 286 (accept_3_3 2 57 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 286 (allA_of_3_1 56 56 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 286 (allA_succ_of_accept 54 55 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 286 (accept_3_3 53 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 286 (accept_3_3 50 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 286 (accept_3_3 47 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 55 286 11 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862
  43 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 286 (accept_3_3 41 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 286 (accept_3_3 38 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 286 (accept_3_3 35 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 55 286 11 3 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 55 286 (accept_3_3 32 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 55 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 55 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 286 (accept_3_3 29 55 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 286 (Polychromatic418967fa.accept_12_4_7_10_1_563
  28 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 286 (accept_3_3 26 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 286 (accept_3_3 23 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 286 11 2 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 286 (accept_3_3 20 55 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 55 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 286
  (Polychromatic418967fa.accept_17_1_4_14_1_8058 18 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 286 (accept_3_3 17 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 286 (accept_3_3 14 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 55 286 11 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 286 (Polychromatic418967fa.accept_16_10_7_14_1_2882 10 55 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 286 (accept_3_3 8 55 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 286 (Polychromatic418967fa.accept_14_7_13_6_1_1177
  7 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 286 (accept_3_3 5 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 286 (accept_3_3 2 55 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 286 (allA_succ_of_accept 53 54 286 (accept_3_3 53 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 286 2 26 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 286 2 25 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 286
  (Polychromatic418967fa.accept_17_15_3_14_1_4230 49 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 286 2 24 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 54 286 (accept_3_3 47 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 286 2 23 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 286 2 22 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 286 2 21 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 286 (accept_3_3 41 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 286 2 20 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 54 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 286 2 19 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 286 2 18 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 286 (accept_3_3 35 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 286 2 17 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 286 2 16 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 286
  (Polychromatic418967fa.accept_20_11_14_6_1_4714 31 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 286 2 15 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 286 (accept_3_3 29 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 286 2 14 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 286 2 13 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 286 2 12 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 286 (accept_3_3 23 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 286 2 11 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 286 2 10 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 286
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 19 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 286 2 9 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 286 (accept_3_3 17 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  286 2 8 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 286 2 7 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 54 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 286 2 6 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 286 (accept_3_3 11 54 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 286 2 5 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 54 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 286 2 4 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 54 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 286 2 3 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 286 (accept_3_3 5 54 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 286 2 2 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 286 2 1 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 286 (allA_of_3_1 53 53 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 286 (allA_succ_of_accept 51 52 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 286 2 25 26 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 286 2 24 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 52 286 (accept_3_3 47 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 52 286 2 23 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 52 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 52 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 286 2 22 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 286 2 21 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 52 286 (accept_3_3 41 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 52 286 2 20 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 52 286 13 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 52 286 2 19 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 286 2 18 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 286 (accept_3_3 35 52 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 286 2 17 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 286
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 286 2 16 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 286 2 15 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 286 (accept_3_3 29 52 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 286 2 14 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 286 (Polychromatic418967fa.accept_17_10_1_14_1_489
  27 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 286 26 1 2 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 286 2 12 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 52 286 (accept_3_3 23 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 52 286 2 11 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 52 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 286 2 10 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 286 2 9 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 286 (accept_3_3 17 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  286 2 8 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 286 2 7 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 13 52 286 13 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 52 286 2 6 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 52 286 (accept_3_3 11 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 52 286 2 5 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 52 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 286 2 4 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 286 2 3 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 286 (accept_3_3 5 52 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 286 2 2 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3
  52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 286 2 1 26 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 52 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 286)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 286 (allA_succ_of_accept 50 51 286
  (accept_3_3 50 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 286 (accept_3_3 47 51 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 286 (accept_3_3 44 51
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 286 (accept_3_3 41 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 286 (accept_3_3 38 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 286 (accept_3_3 35 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 286 (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 286 (accept_3_3 32 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 286 (accept_3_3 29 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 286 (accept_3_3 26 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 286 (accept_3_3 23 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 286 (accept_3_3 20 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 286 (accept_3_3 17 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 286 (Polychromatic418967fa.accept_19_16_13_1_1_12406 16 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 286 (accept_3_3 14 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 286 (accept_3_3 11 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 286 (accept_3_3 8 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 286 (accept_3_3 5 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 286 (accept_3_3 2 51 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 286)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 286 (allA_of_3_1 50 50 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 286
  (allA_succ_of_accept 48 49 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 286 (accept_3_3 47 49 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 286 (accept_3_3 44 49
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 286 (accept_3_3 41 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 286 (accept_3_3 38 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 286 (accept_3_3 35 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 286 (Polychromatic418967fa.accept_19_15_11_1_1_12437 34 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 286 (accept_3_3 32 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 286 (accept_3_3 29 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 286 (accept_3_3 26 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 286 (accept_3_3 23 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 286 (accept_3_3 20 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 286 (accept_3_3 17 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 286 (accept_3_3 14 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 286 (accept_3_3 11 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 286 (accept_3_3 8 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 286 (accept_3_3 5 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 286 (accept_3_3 2 49 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 286)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 286 (allA_succ_of_accept 47 48 286 (accept_3_3 47 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 286 2 23 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 45 48 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 286 2 22 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 286 2 21 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 48 286 (accept_3_3 41 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 286 2 20 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 286 (Polychromatic418967fa.accept_21_18_6_13_1_7148 39 48 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 286 2 19 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 286 2 18 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 48 286 (accept_3_3 35 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 286 2 17 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 48 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 286 2 16 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 286 2 15 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 286 (accept_3_3 29 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 286 2 14 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 27 48 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 286 2 13 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 286
  (Polychromatic418967fa.accept_19_6_10_1_1_5394 25 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 286 2 12 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 286 (accept_3_3 23 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 286 2 11 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 48 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 48 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 286 2 10 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 286 2 9 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 286 (accept_3_3 17 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  286 2 8 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 286 2 7 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 48 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 286 2 6 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 286 (accept_3_3 11 48 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 286 2 5 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 286
  (Polychromatic418967fa.accept_18_9_12_16_1_7323 9 48 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 286 2 4 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 286 (Polychromatic418967fa.accept_19_7_10_1_1_5382 7 48 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 286 2 3 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 286 (accept_3_3 5 48 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 286 2 2 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 286 2 1 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  286)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 286 (allA_of_3_1 47 47 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 286 (allA_succ_of_accept 45 46 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45
  46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 286 2 22 23 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 286
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 43 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 286 2 21 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 46 286 (accept_3_3 41 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 46 286 2 20 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 46 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 286 2 19 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 286 2 18 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 286 (accept_3_3 35 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 286 2 17 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 286 2 16 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 286 2 15 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 286 (accept_3_3 29 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 286 2 14 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 286 (Polychromatic418967fa.accept_21_6_4_13_1_8740 27 46 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 286 2 13 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 286
  (Polychromatic418967fa.accept_27_25_19_16_1_17519 25 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 46 286 2 12 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 46 286 (accept_3_3 23 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 286 2 11 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 286 2 10 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 286 2 9 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 286 (accept_3_3 17 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  286 2 8 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 286 2 7 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 286 2 6 23 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 286 (accept_3_3 11 46 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 286 2 5 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 286 2 4 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 286 (Polychromatic418967fa.accept_19_7_8_1_1_4028 7 46 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 286 2 3 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 286 (accept_3_3 5 46 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 286 2 2 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 286 2 1 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 1
  46 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  286)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 286 (allA_succ_of_accept 44 45 286 (accept_3_3 44 45
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 286 (accept_3_3 41 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 286 (Polychromatic418967fa.accept_19_2_7_1_1_2808 40 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 286 (accept_3_3 38 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 286
  (Polychromatic418967fa.accept_23_13_22_10_1_9668 36 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 286 (accept_3_3 35 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 33 45
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 286 (accept_3_3 32 45 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 286 (accept_3_3 29 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 286 (Polychromatic418967fa.accept_23_5_22_10_1_17518 28 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 286 (accept_3_3 26 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 286 (accept_3_3 23 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 286 (Polychromatic418967fa.accept_25_22_20_11_1_17517 22 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 286 (accept_3_3 20 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 286 (accept_3_3 17 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 286 (accept_3_3 14 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 286
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 286 (accept_3_3 11 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 45 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 286 (accept_3_3 8 45 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 286 (accept_3_3 5 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 286 (accept_3_3 2 45 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 286))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  286 (allA_of_3_1 44 44 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 286 (allA_succ_of_accept 42 43 286
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 286 (accept_3_3 41 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 286 (accept_3_3 38 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 286
  (Polychromatic418967fa.accept_23_13_20_10_1_16083 36 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 43 286 (accept_3_3 35 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 43 286 (Polychromatic418967fa.accept_19_15_5_1_1_5360 34 43 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 286 (accept_3_3 32 43 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 286
  (Polychromatic418967fa.accept_19_12_5_1_1_11093 31 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 286 (accept_3_3 29 43 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 286 (accept_3_3 26 43
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3
  25 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 286
  (Polychromatic418967fa.accept_23_1_20_10_1_9665 24 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 286 (accept_3_3 23 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 286 (Polychromatic418967fa.accept_17_5_9_14_1_4282 22 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 286 (accept_3_3 20 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 286 (accept_3_3 17 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 286 (accept_3_3 14 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 286 (accept_3_3 11 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 286 (accept_3_3 8 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 286
  (Polychromatic418967fa.accept_19_6_5_1_1_2765 6 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 286 (accept_3_3 5 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 43 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 286 (accept_3_3 2 43 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 286)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 286 (allA_succ_of_accept 41 42 286 (accept_3_3 41 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 286 2 20 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 286 2 19 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 286 2 18 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 42 286 (accept_3_3 35 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 286 2 17 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 42 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 286 2 16 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 286 2 15 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 286 (accept_3_3 29 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 286 2 14 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 42 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 286 2 13 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 286
  (Polychromatic418967fa.accept_27_25_15_16_1_17516 25 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 42 286 2 12 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 42 286 (accept_3_3 23 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 286 2 11 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 42 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 286 2 10 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 286 2 9 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 286 (accept_3_3 17 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  286 2 8 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 286 2 7 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 42 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 286 2 6 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 286 (accept_3_3 11 42 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 286 2 5 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 286 2 4 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 286 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 42 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 286 2 3 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 286 (accept_3_3 5 42 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 286 2 2 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 286 2 1 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  286)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 286 (allA_of_3_1 41 41 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 286 (allA_succ_of_accept 39 40 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 286 2 19 20 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 286 2 18 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 40 286 (accept_3_3 35 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 40 286 2 17 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 40 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 286 2 16 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 286 2 15 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 286 (accept_3_3 29 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 40 286 2 14 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 40 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 286 2 13 20 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 286 2 12 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 40 286 (accept_3_3 23 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 286 2 11 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 286 2 10 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 286 2 9 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 286 (accept_3_3 17 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  286 2 8 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 286 2 7 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 40 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 40 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 286 2 6 20 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 286 (accept_3_3 11 40 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 286 2 5 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 40 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 286 2 4 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 286 2 3 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 286 (accept_3_3 5 40 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 286 2 2 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 286 2 1 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  286)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 286 (allA_succ_of_accept 38 39 286 (accept_3_3 38 39 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 286 (accept_3_3 35 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 286 (accept_3_3 32 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 286 (accept_3_3 29 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 286 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 39 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 286 13 2 3 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 286 (accept_3_3 23 39 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 286 (accept_3_3 20 39
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  19 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 286 (accept_3_3 17 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 286 (accept_3_3 14 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 286 13 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 39 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 286 (accept_3_3 11 39 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 286 (accept_3_3 8 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 286 (accept_3_3 5 39 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  39 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 286 (accept_3_3 2 39 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  286))))))))))))))))))))))))))))))))))))))) (allB_succ 38 286 (allA_of_3_1 38 38 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 286 (allA_succ_of_accept 36 37 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 286 (accept_3_3 35 37 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 286
  (Polychromatic418967fa.accept_27_7_10_16_1_17515 34 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 286 (accept_3_3 32 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 286 (accept_3_3 29 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 286 (accept_3_3 26 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 286 (accept_3_3 23 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 286 (accept_3_3 20 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 286 (accept_3_3 17 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 286 (accept_3_3 14 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 286 (accept_3_3 11 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 286 (accept_3_3 8 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 286 (accept_3_3 5 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 286 (accept_3_3 2 37 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 286))))))))))))))))))))))))))))))))))))) (allB_succ 36 286
  (allA_succ_of_accept 35 36 286 (accept_3_3 35 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  286 2 17 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 36 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 286 2 16 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 31 36 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 286 2 15 18 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 286 (accept_3_3 29 36 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 286 2 14 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 286
  (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 286 2 13 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 36 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 286 2 12 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 286 (accept_3_3 23 36 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 286 2 11 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164
  21 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 286 2 10 18 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 286 2 9 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 286 (accept_3_3 17 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  286 2 8 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 286 2 7 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 36 286 (Polychromatic418967fa.accept_27_13_9_16_1_17514 13 36 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 286 2 6 18 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 286 (accept_3_3 11 36 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 286 2 5 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 286 2 4 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 36 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 286 2 3 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 286 (accept_3_3 5 36 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 286 2 2 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 36 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 286 2 1 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 286 (Polychromatic418967fa.accept_16_1_4_14_1_1896 1
  36 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  286)))))))))))))))))))))))))))))))))))) (allB_succ 35 286 (allA_of_3_1 35 35 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 34 286 (allA_succ_of_accept 33 34 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 33 34 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 286 2 16 17 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 286
  (Polychromatic418967fa.accept_20_11_14_6_1_4714 31 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 286 2 15 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 34 286 (accept_3_3 29 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 34 286 2 14 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 34 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 286 2 13 17 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 286 2 12 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 286 (accept_3_3 23 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 286 2 11 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 286 (Polychromatic418967fa.accept_19_2_15_1_1_3977 21 34 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 286 2 10 17 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 286
  (Polychromatic418967fa.accept_20_19_14_6_1_4726 19 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 286 2 9 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 286 (accept_3_3 17 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  286 2 8 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 286 2 7 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 286 (Polychromatic418967fa.accept_23_13_11_10_1_17513 13 34 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 286 2 6 17 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 286 (accept_3_3 11
  34 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 286 2 5 17 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 286
  (Polychromatic418967fa.accept_20_9_14_6_1_320 9 34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 286 2 4 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 286 (Polychromatic418967fa.accept_25_7_9_11_1_17512 7 34 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 286 2 3 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 286 (accept_3_3 5 34 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 286 2 2 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 34 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 286 2 1 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 286 (Polychromatic418967fa.accept_20_1_14_6_1_4725 1
  34 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 286))))))))))))))))))))))))))))))))))
  (allB_succ 33 286 (allA_succ_of_accept 32 33 286 (accept_3_3 32 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 286 (accept_3_3 29 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 286 (accept_3_3 26 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 286 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 33 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 286 (accept_3_3 23 33 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 286 11 2 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 33 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 286 (accept_3_3 20 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 286 (accept_3_3 17 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 286 (Polychromatic418967fa.accept_24_16_9_22_1_14220 16 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 286 (accept_3_3 14 33 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 33 286 11 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 33 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 286 (accept_3_3 8 33 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 286 (accept_3_3 5 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 286 (accept_3_3 2 33 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 286))))))))))))))))))))))))))))))))) (allB_succ 32 286
  (allA_of_3_1 32 32 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 286 (allA_succ_of_accept 30 31 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 286 (accept_3_3 29 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 286 (accept_3_3 26 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 286 (accept_3_3 23 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 286 (accept_3_3 20 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 286 (accept_3_3 17 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 286 (accept_3_3 14 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 286 (accept_3_3 11 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 286 (accept_3_3 8 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 286 (accept_3_3 5 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 286 (accept_3_3 2 31 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 286))))))))))))))))))))))))))))))) (allB_succ 30 286
  (allA_succ_of_accept 29 30 286 (accept_3_3 29 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  286 2 14 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 30 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 286 2 13 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 286 2 12 15 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 286 (accept_3_3 23 30 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 286 2 11 15 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 286 2 10 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 286 2 9 15 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 286 (accept_3_3 17 30 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 286 2 8 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 286 2 7 15 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 286 2 6 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 286 (accept_3_3 11 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30
  286 2 5 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  30 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 30 286 2 4 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 30 286 (Polychromatic418967fa.accept_21_7_9_13_1_5612 7 30 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 286 2 3 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 286 (accept_3_3 5 30 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 286 2 2 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 30 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 286 2 1 15 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 286)))))))))))))))))))))))))))))) (allB_succ 29 286 (allA_of_3_1 29 29 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 286 (allA_succ_of_accept 27 28 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 28 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 286 2 13 14 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 286 2 12 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 28 286 (accept_3_3 23 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 28 286 2 11 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 286 2 10 14 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 286 2 9 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 286 (accept_3_3 17 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  286 2 8 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 286 2 7 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 28 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 286 2 6 14 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 286 (accept_3_3 11 28 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 286 2 5 14 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 286
  (Polychromatic418967fa.accept_21_9_7_13_1_8742 9 28 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 286 2 4 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 286 2 3 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 286 (accept_3_3 5 28 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 286 2 2 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 286 2 1 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  28 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 286))))))))))))))))))))))))))))
  (allB_succ 27 286 (allA_succ_of_accept 26 27 286 (accept_3_3 26 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 286 (Polychromatic418967fa.accept_17_7_10_14_1_8022 24 27
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 286 (accept_3_3 23 27 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 286
  (Polychromatic418967fa.accept_17_5_10_14_1_2083 22 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 27 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 286 (accept_3_3 20 27 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 27 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 286 (Polychromatic418967fa.accept_12_6_3_10_1_224
  18 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 286 (accept_3_3 17
  27 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 286
  (Polychromatic418967fa.accept_19_16_8_1_1_8259 16 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 27 286 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 27 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 286 (accept_3_3 14 27 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 286
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 286 (accept_3_3 11 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 286 (Polychromatic418967fa.accept_25_10_2_11_1_17511 10 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 286 (accept_3_3 8 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 286 (accept_3_3 5 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 27 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 286 (accept_3_3 2 27 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 286))))))))))))))))))))))))))) (allB_succ 26 286
  (allA_of_3_1 26 26 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 286 (allA_succ_of_accept 24 25 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 286 (accept_3_3 23 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 286 (accept_3_3 20 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 286
  (Polychromatic418967fa.accept_19_18_6_1_1_12398 18 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 286 (accept_3_3 17 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 286 (accept_3_3 14 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 25 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 286 (accept_3_3 11 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 286 (accept_3_3 8 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 286 (accept_3_3 5 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  286 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 286 (accept_3_3 2 25 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 25 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 286))))))))))))))))))))))))) (allB_succ 24 286
  (allA_succ_of_accept 23 24 286 (accept_3_3 23 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  286 2 11 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 24 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 286 2 10 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 24 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 286 2 9 12 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 286 (accept_3_3 17 24 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 286 2 8 12 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 286 2 7 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 286 2 6 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 286 (accept_3_3 11 24 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 286 2 5 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 286 2 4 12 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 286 2 3 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 286 (accept_3_3 5 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 286
  2 2 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24
  286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 286 2 1 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 286)))))))))))))))))))))))) (allB_succ 23 286 (allA_of_3_1 23 23 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 286 (allA_succ_of_accept 21 22 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 286 2 10 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 286 2 9 11 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 286 (accept_3_3 17 22 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 286 2 8 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  22 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 286 2 7 11 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 286
  (Polychromatic418967fa.accept_23_13_22_10_1_9668 13 22 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 22 286 2 6 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 286 11 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 286 2 5 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 286 2 4 11 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 22 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 286 2 3 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 286 (accept_3_3 5 22 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 286
  2 2 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 22 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 286 2 1 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 286)))))))))))))))))))))) (allB_succ 21 286 (allA_succ_of_accept 20 21
  286 (accept_3_3 20 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 286 (accept_3_3 17 21 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 286 (Polychromatic418967fa.accept_20_16_1_6_1_6196 16 21 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 286 (accept_3_3 14 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 286 (accept_3_3 11 21 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 286 (accept_3_3 8 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 286 (accept_3_3 5 21 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 286 (accept_3_3 2 21 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 286))))))))))))))))))))) (allB_succ 20
  286 (allA_of_3_1 20 20 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 286 (allA_succ_of_accept 18 19 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 286 (accept_3_3 17 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 286 (accept_3_3 14 19 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 286 (accept_3_3 11 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 286 (accept_3_3 8 19 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 286 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 19 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 286 (accept_3_3 5 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 286 (accept_3_3 2 19 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 286))))))))))))))))))) (allB_succ 18 286 (allA_succ_of_accept 17
  18 286 (accept_3_3 17 18 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 286 2 8 9 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 18 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 286 2 7 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 286 2 6 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 286 (accept_3_3 11 18 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 286 2 5 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 286 2 4 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 286 (Polychromatic418967fa.accept_19_7_18_1_1_1662 7
  18 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 286 2 3 9 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 286 (accept_3_3 5 18
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 286 2 2 9 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 286 2 1 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 286 (Polychromatic418967fa.accept_25_1_18_11_1_15900 1 18 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 286)))))))))))))))))) (allB_succ 17 286 (allA_of_3_1 17 17 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 286 (allA_succ_of_accept 15 16 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 286 2 7 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 16 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 286 2 6 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 286 (accept_3_3 11 16 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 286 2 5 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 286 (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 16 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 286 2 4 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 286 2 3 8 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 286 (accept_3_3 5 16
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 286 2 2 8 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 286 2 1 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 286)))))))))))))))) (allB_succ 15 286 (allA_succ_of_accept 14 15 286
  (accept_3_3 14 15 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 286 (accept_3_3 11 15 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 15 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 286 (accept_3_3 8 15 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 15 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 286 (accept_3_3 5 15 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 286 (accept_3_3 2 15 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 286))))))))))))))) (allB_succ 14 286 (allA_of_3_1 14 14 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 286 (allA_succ_of_accept 12 13 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 286 (accept_3_3 11 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 286 (accept_3_3 8 13 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 286 (accept_3_3 5 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 13 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 286 (accept_3_3 2 13 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 286))))))))))))) (allB_succ 12 286
  (allA_succ_of_accept 11 12 286 (accept_3_3 11 12 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  286 2 5 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  12 286 (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 12 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 286 2 4 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 286 (Polychromatic418967fa.accept_19_7_12_1_1_6830 7 12 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 286 2 3 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 286 (accept_3_3 5 12 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 286 2 2 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 3 12 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 286 2 1 6 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 286)))))))))))) (allB_succ 11 286 (allA_of_3_1 11 11 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 286 (allA_succ_of_accept 9 10 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 286 2 4 5 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7
  10 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 286 2 3 5 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 286 (accept_3_3 5 10
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 286 2 2 5 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 286 2 1 5 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 286 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 10 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 286)))))))))) (allB_succ 9 286 (allA_succ_of_accept 8 9 286 (accept_3_3 8
  9 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 286 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 9 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 286 (accept_3_3 5 9 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 286 (accept_3_3 2 9 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 286))))))))) (allB_succ 8 286 (allA_of_3_1 8 8 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 286 (allA_succ_of_accept 6 7 286
  (Polychromatic418967fa.accept_15_6_7_1_1_93 6 7 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 286 (accept_3_3 5 7 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 286
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 286 (accept_3_3 2 7 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 286))))))) (allB_succ 6 286 (allA_succ_of_accept 5 6 286
  (accept_3_3 5 6 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 286 2 2 3 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 286 2 1 3 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 286)))))) (allB_succ 5 286 (allA_of_3_1 5 5 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 286 (allA_succ_of_accept 3 4 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 286 2 1 2 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 286)))) (allB_succ 3 286 (allA_succ_of_accept 2 3 286 (accept_3_3 2 3 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 286))) (allB_succ 2 286 (allA_of_3_1 2 2 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


