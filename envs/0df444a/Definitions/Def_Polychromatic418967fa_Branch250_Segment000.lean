-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch250_Segment000
-- name    : Polychromatic418967fa_Branch250_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:40:20.7919+00:00
-- url     : https://prove2.me/theorems/35deec8f-69cc-49a6-add3-336ff56824a4
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

def Polychromatic418967fa.branch_250_segment_000 : allB 124 250 :=
  allB_succ 123 250 (allA_succ_of_accept 122 123 250 (accept_3_3 122 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 120 123
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 250 (accept_3_3 119 123
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 118 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 250 (accept_3_3 116 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 250 (Polychromatic418967fa.accept_7_2_4_5_1_313
  114 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 250 (accept_3_3
  113 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 112 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 123 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 111 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 250 (accept_3_3 110 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 250
  (Polychromatic418967fa.accept_16_12_11_10_1_1667 108 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 123 250 (accept_3_3 107 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 106 123 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 123 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 250 (accept_3_3 104 123 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1
  103 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 102 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 123 250 (accept_3_3 101 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 123 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 250 (accept_3_3 98 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 250
  (Polychromatic418967fa.accept_13_5_6_3_1_868 96 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 250 (accept_3_3 95 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 250 (accept_3_3 92 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 90 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 250 (accept_3_3 89 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 250 (Polychromatic418967fa.accept_13_10_6_3_1_1515 88 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 250 (Polychromatic418967fa.accept_13_9_6_3_1_1514 87 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 250 (accept_3_3 86 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 123 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 250 (accept_3_3 83 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 250 (accept_3_3 80 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 250 (accept_3_3 77 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 250 (accept_3_3 74 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 250 (accept_3_3 71 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 250 (Polychromatic418967fa.accept_13_5_6_3_1_868 70 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 250 (accept_3_3 68 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 250 (accept_3_3 65 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 250 (Polychromatic418967fa.accept_16_15_11_10_1_3639 63 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 250 (accept_3_3 62 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 123 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 250
  (Polychromatic418967fa.accept_11_5_2_8_1_866 60 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 250 (accept_3_3 59 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 250 (accept_3_3 56 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 250 (accept_3_3 53 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 250 (Polychromatic418967fa.accept_15_7_3_10_1_817 52 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 250 (accept_3_3 50 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 250 (accept_3_3 47 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 250 (accept_3_3 44 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 250 (accept_3_3 41 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 250 (accept_3_3 38 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 250 (accept_3_3 35 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 250 (accept_3_3 32 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 250 (accept_3_3 29 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 250 (accept_3_3 26 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 250
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 250 (accept_3_3 23 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 250 (accept_3_3 20 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 250 (accept_3_3 17 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 250 (accept_3_3 14 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 250 (accept_3_3 11 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 250 (accept_3_3 8 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 250 (accept_3_3 5 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 250 (accept_3_3 2 123 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 250 (allA_of_3_1 122 122 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 250
  (allA_succ_of_accept 120 121 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 120 121 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 250 (accept_3_3 119 121 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 118 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 250 (Polychromatic418967fa.accept_6_3_1_4_1_25
  117 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 121 250 (accept_3_3
  116 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 115 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 121 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 114 121 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 250 (accept_3_3 113 121 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 121 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 112 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 250 (accept_3_3 110 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 109 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 250 (accept_3_3 107 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 250 (Polychromatic418967fa.accept_17_4_2_12_1_6554 106
  121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 250 (accept_3_3 104 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 250 (accept_3_3 101 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 121 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 250 (accept_3_3 98 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 97 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 250 (accept_3_3 95 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 250 (accept_3_3 92 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 250 (Polychromatic418967fa.accept_13_12_4_3_1_1528 90 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 250 (accept_3_3 89 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 121 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 250 (accept_3_3 86 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 85 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 250 (accept_3_3 83 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 250 (accept_3_3 80 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 250 (accept_3_3 77 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 250 (accept_3_3 74 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 250 (accept_3_3 71 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 250 (Polychromatic418967fa.accept_19_13_7_3_1_9798 70 121
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 250 (accept_3_3 68 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 250 (accept_3_3 65 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 250 (accept_3_3 62 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 250 (Polychromatic418967fa.accept_17_10_2_12_1_1070 61 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 250 (accept_3_3 59 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 250 (Polychromatic418967fa.accept_15_13_1_10_1_816 58 121 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 250 (accept_3_3 56 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 250 (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 250 (accept_3_3 53 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 121 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 250 (accept_3_3 50 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 250 (Polychromatic418967fa.accept_14_7_9_12_1_3975 49 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 250 (accept_3_3 47 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 250 (accept_3_3 44 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 250 (accept_3_3 41 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 250 (accept_3_3 38 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 250 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 250 (accept_3_3 35 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 250 (Polychromatic418967fa.accept_19_15_7_3_1_4143 34 121
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 250 (accept_3_3 32 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 250 (accept_3_3 29 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 250 (accept_3_3 26 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 250 (accept_3_3 23 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 250 (accept_3_3 20 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 250 (accept_3_3 17 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 250 (accept_3_3 14 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 250 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 250 (accept_3_3 11 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 250 (accept_3_3 8 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 250 (accept_3_3 5 121 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 250 (accept_3_3 2 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 250 (allA_succ_of_accept 119 120 250 (accept_3_3 119 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 120 250 2 59 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 120 250 (Polychromatic418967fa.accept_17_15_1_12_1_7910 117 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 250 2 58 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 115 120 250 5 23 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 120 250 2 57 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 250
  (accept_3_3 113 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 250 2 56 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 120 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 111 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 120 250 10 11 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 120 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 109 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 250 2 54 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 250 (accept_3_3 107 120 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 250 2 53 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 250 5 21 24 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 250 2 52 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 103 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 250 2 51 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 250 (accept_3_3 101 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 250 10 10 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 250 (Polychromatic418967fa.accept_18_9_12_16_1_7323 99 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 250 2 49 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 97 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 250 2 48 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 120 250 5 19 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 250 2 47 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 250 (Polychromatic418967fa.accept_19_17_6_3_1_9830 93 120
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 250 2 46 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 250 10 9 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 250 (accept_3_3 89 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 250 2 44 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 250 2 43 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 250 5 17 24 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 250 2 42 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 250 (accept_3_3 83
  120 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 250 2 41 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 250 10 8 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 250 (Polychromatic418967fa.accept_31_17_27_2_1_15094 79 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 250 2 39 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 250 (accept_3_3 77 120 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 250 2 38 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 250 5 15 24 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 250 2 37 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 73 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 250 2 36 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 250 (accept_3_3 71 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 250 10 7 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 250 2 34 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 250 2 33 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 120 250 5 13 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 250 2 32 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 250 (Polychromatic418967fa.accept_18_9_12_16_1_7323 63 120
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 250 2 31 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 250
  (Polychromatic418967fa.accept_19_4_6_3_1_15078 61 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 250 10 6 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 250 (accept_3_3 59 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 250 2 29 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 120 250 (Polychromatic418967fa.accept_17_6_1_12_1_4115 57 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 250 2 28 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 250 5 11 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 250 2 27 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 250
  (accept_3_3 53 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 250 2 26 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 250 10 5 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 250 2 24 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 250 (accept_3_3 47 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 250 2 23 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 250 5 9 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 250 2 22 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 250
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 43 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 250 2 21 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 250 (accept_3_3 41 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 250 10 4 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 250 2 19 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 250 2 18 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 120 250 5 7 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 120 250 2 17 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 120 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 250 2 16 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 250 10 3 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 250 (accept_3_3 29 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 250 2 14 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 250 2 13 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 250 5 5 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 250 2 12 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 250 (accept_3_3 23 120 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 250 2 11 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 250
  (Polychromatic418967fa.accept_19_2_6_3_1_4182 21 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 250 10 2 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 250 2 9 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 250 (accept_3_3 17 120 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 250 2 8 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 250 5 3 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 250 2 7 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 250 2 6 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 120 250 (accept_3_3 11 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 250 10 1 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 250 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 120 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 250 2 4 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 250
  (Polychromatic418967fa.accept_19_7_6_3_1_6998 7 120 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 250 2 3 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 120 250 5 1 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 120 250 2 2 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 120 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 250 2 1 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 250 (allA_of_3_1 119 119 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 250
  (allA_succ_of_accept 117 118 250 (Polychromatic418967fa.accept_15_12_13_10_1_812 117 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 250 2 58 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 250
  (Polychromatic418967fa.accept_13_11_1_3_1_910 115 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 118 250 2 57 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 118 250 (accept_3_3 113 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 250 2 56 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 111 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 250 2 55 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 109 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 118 250 2 54 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 118 250 (accept_3_3 107 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 250 2 53 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 105 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 250 2 52 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 103 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 250 2 51 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 250 (accept_3_3 101 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 250 2 50 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 250 2 49 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 250
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 97 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 250 2 48 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 250 (accept_3_3 95 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 250 2 47 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 93 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 250 2 46 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 250
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 118 250 2 45 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 118 250 (accept_3_3 89 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 250 2 44 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 250 2 43 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 85 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 250 2 42 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 250 (accept_3_3 83 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 250 2 41 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 250 2 40 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 250
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 118 250 2 39 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 118 250 (accept_3_3 77 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 250 2 38 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 250 2 37 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 250
  (Polychromatic418967fa.accept_18_1_10_16_1_566 73 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 250 2 36 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 250 (accept_3_3 71 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 250 2 35 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 250 2 34 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 250 2 33 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 250 (accept_3_3 65 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 250 2 32 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 250 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 250 2 31 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 250
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 118 250 2 30 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 118 250 (accept_3_3 59 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 250 2 29 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 250 2 28 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 250
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 55 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 118 250 2 27 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 118 250 (accept_3_3 53 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 250 2 26 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 250 2 25 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 250 2 24 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 250 (accept_3_3 47 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 250 2 23 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 250 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 250 2 22 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 250 2 21 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 250 (accept_3_3 41 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 250 2 20 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 250 2 19 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 250
  (Polychromatic418967fa.accept_13_11_1_3_1_910 37 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 250 2 18 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 250 (accept_3_3 35 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 250 2 17 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 250 2 16 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 250 2 15 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 250 (accept_3_3 29 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 250 2 14 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 250 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 250 2 13 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 250 2 12 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 250 (accept_3_3 23 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 250 2 11 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 250 2 10 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 250
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 250 2 9 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 250 (accept_3_3 17 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 250 2 8 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 118 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 250 2 7 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 250 2 6 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 250 (accept_3_3 11 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 250 2 5 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 250 (Polychromatic418967fa.accept_27_9_10_7_1_15093 9 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 250 2 4 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 250
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 250 2 3 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 250 (accept_3_3 5 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  250 2 2 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 250 2 1 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 118 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 250 (allA_succ_of_accept 116 117 250 (accept_3_3 116 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 114 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 250 (accept_3_3 113 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 250
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 112 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 250 (accept_3_3 110 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 117 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 250
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 108 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 117 250 (accept_3_3 107 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 250 (Polychromatic418967fa.accept_21_1_12_19_1_7721 106 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 250
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 105 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 250 (accept_3_3 104 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 102 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 250 (accept_3_3 101 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 250
  (Polychromatic418967fa.accept_22_12_7_8_1_8957 100 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 250 (accept_3_3 98 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 250
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 96 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 250 (accept_3_3 95 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 94 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 250
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 93 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 250 (accept_3_3 92 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 250 (accept_3_3 89 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 250
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 88 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 250 (accept_3_3 86 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 250
  (Polychromatic418967fa.accept_15_9_12_10_1_809 84 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 250 (accept_3_3 83 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 250 (Polychromatic418967fa.accept_15_7_12_10_1_4335 82 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 250 (accept_3_3 80 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 117 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 78 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 250 (accept_3_3 77 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 250 (Polychromatic418967fa.accept_16_12_5_10_1_3561 76 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 250 (accept_3_3 74 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 250
  (Polychromatic418967fa.accept_21_9_12_19_1_12172 72 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 250 (accept_3_3 71 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 250 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 250 (accept_3_3 68 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 250 (accept_3_3 65 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 117 250 (Polychromatic418967fa.accept_21_1_12_19_1_7721 64 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 250 (accept_3_3 62 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 250 (Polychromatic418967fa.accept_16_12_5_10_1_3561 60 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 250 (accept_3_3 59 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 250 (Polychromatic418967fa.accept_15_13_12_10_1_4352 58
  117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 250
  (Polychromatic418967fa.accept_21_15_12_19_1_10724 57 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 250 (accept_3_3 56 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 250 (accept_3_3 53 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 250
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 52 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 250 (accept_3_3 50 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 250
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 250 (accept_3_3 47 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 250 (Polychromatic418967fa.accept_16_14_5_10_1_3622 46 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 250 (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 250 (accept_3_3 44 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 250 (accept_3_3 41 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 250 (Polychromatic418967fa.accept_22_18_7_8_1_12020 40 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 250 (accept_3_3 38 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 250
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 250 (accept_3_3 35 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 250 (Polychromatic418967fa.accept_22_12_7_8_1_8957 34 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 250 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 250 (accept_3_3 32 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 250 (accept_3_3 29 117 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 250 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 250 (accept_3_3 26 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 250 (accept_3_3 23 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 250 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 250
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 21 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 250 (accept_3_3 20 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 250 (accept_3_3 17 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 250 (Polychromatic418967fa.accept_22_16_7_8_1_15092 16 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 250 (accept_3_3 14 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 250 (Polychromatic418967fa.accept_16_12_5_10_1_3561 12 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 250 (accept_3_3 11 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 117
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 250
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 250 (accept_3_3 8 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 250 (accept_3_3 5 117 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 117 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 250 (accept_3_3 2 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 250 (allA_of_3_1 116 116 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 250
  (allA_succ_of_accept 114 115 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 114 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 250 (accept_3_3 113 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 112 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 115 250 5 22 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 250
  (Polychromatic418967fa.accept_16_12_3_10_1_3524 108 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 115 250 (accept_3_3 107 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 115 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 106 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 115 250 5 21 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 115 250 (accept_3_3 104 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 250 (Polychromatic418967fa.accept_14_5_3_12_1_324 103 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 250
  (Polychromatic418967fa.accept_11_3_5_8_1_458 102 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 250 (accept_3_3 101 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 115 250 5 20 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 115 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 250 (accept_3_3 98 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 250 (Polychromatic418967fa.accept_13_5_11_3_1_902
  96 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 115 250 5 19 23 50
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 250
  (Polychromatic418967fa.accept_18_4_7_16_1_2307 94 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 250 (accept_3_3 92 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 115 250 (Polychromatic418967fa.accept_11_3_5_8_1_458 91 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 115 250 5 18 23 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 115 250 (accept_3_3 89 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 250 (Polychromatic418967fa.accept_12_4_7_10_1_563
  88 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 250 (accept_3_3 86 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  115 250 5 17 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 115 250 (Polychromatic418967fa.accept_17_16_13_12_1_4092 84 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 250 (accept_3_3 83 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 250 (Polychromatic418967fa.accept_19_6_1_3_1_11225 82 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 115 250 5 16 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 115 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 78
  115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 250 (accept_3_3 77
  115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 250
  (Polychromatic418967fa.accept_12_4_7_10_1_563 76 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 115 250 5 15 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 115 250 (accept_3_3 74 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 250 (accept_3_3 71 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 115 250 5 14 23 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 115 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 250 (accept_3_3 68 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 250 (Polychromatic418967fa.accept_13_2_11_3_1_873 67 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 250 (Polychromatic418967fa.accept_13_1_11_3_1_901 66 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 250 5 13 23 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 250 (accept_3_3 62 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 250 5 12 23 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 250 (accept_3_3 59 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 250 (accept_3_3 56 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  115 250 5 11 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 115 250 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 250 (accept_3_3 53 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 115 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 250 5 10 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 250
  (Polychromatic418967fa.accept_19_10_1_3_1_12548 48 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 115 250 (accept_3_3 47 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 115 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 115 250 5 9 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 250 (accept_3_3 44 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 250
  (Polychromatic418967fa.accept_19_4_1_3_1_15091 42 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 250 (accept_3_3 41 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  115 250 5 8 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 115 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 115 250 (accept_3_3 38 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 250 5 7 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 250
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 250 (accept_3_3 32 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 250 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 250 5 6 23 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 250 (accept_3_3 29 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 250 (Polychromatic418967fa.accept_12_4_7_10_1_563
  28 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 250 (accept_3_3 26 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  115 250 5 5 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 115 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 250 (accept_3_3 23 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 250 5 4 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 250
  (Polychromatic418967fa.accept_14_5_3_12_1_324 19 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 250 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 250 (accept_3_3 17 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 250 5 3 23 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 250 (accept_3_3 14 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 250
  (Polychromatic418967fa.accept_16_12_3_10_1_3524 12 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 115 250 (accept_3_3 11 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 115 250 5 2 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 250 (accept_3_3 8 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 115 250 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 115 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 250
  (Polychromatic418967fa.accept_19_6_1_3_1_11225 6 115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 115 250 5 1 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 115 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 115 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 250 (accept_3_3 2 115 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  115 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 250 (allA_succ_of_accept 113 114 250 (accept_3_3 113 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 114 250 2 56 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 114 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 111 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 250 2 55 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 109 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 250 2 54 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 250 (accept_3_3 107 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 250 2 53 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 105 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 250 2 52 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 103 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 250 2 51 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 250 (accept_3_3 101 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 250 2 50 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 99 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 250 2 49 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 250
  (Polychromatic418967fa.accept_13_6_10_3_1_897 97 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 250 2 48 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 250 (accept_3_3 95 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 250 2 47 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 250 2 46 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 250 2 45 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 250 (accept_3_3 89 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 250 2 44 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 250 2 43 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 250 2 42 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 250 (accept_3_3 83 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 250 2 41 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 250 2 40 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 250
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 79 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 250 2 39 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 250 (accept_3_3 77 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 250 2 38 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 250 2 37 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 250 2 36 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 250 (accept_3_3 71 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 250 2 35 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 250 2 34 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 67 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 250 2 33 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 250 (accept_3_3 65 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 250 2 32 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 250 2 31 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 250
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 61 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 250 2 30 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 250 (accept_3_3 59 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 250 2 29 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 250 2 28 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 250 2 27 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 250 (accept_3_3 53 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 250 2 26 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 250 2 25 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 250 2 24 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 250 (accept_3_3 47 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 250 2 23 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 250 2 22 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 250
  (Polychromatic418967fa.accept_22_21_4_8_1_12043 43 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 114 250 2 21 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 114 250 (accept_3_3 41 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 250 2 20 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 250 2 19 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 250 2 18 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 250 (accept_3_3 35 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 250 2 17 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 250 2 16 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 250 2 15 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 250 (accept_3_3 29 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 250 2 14 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 250 2 13 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 250 2 12 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 250 (accept_3_3 23 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 250 2 11 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 250 2 10 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 250 2 9 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 250 (accept_3_3 17 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 250 2 8 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 250 2 7 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 250 2 6 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 250 (accept_3_3 11 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 250 2 5 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 250 2 4 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 250
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 250 2 3 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 250 (accept_3_3 5 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114
  250 2 2 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  114 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 114 250 2 1 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 114 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 114 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 250 (allA_of_3_1 113 113 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 250
  (allA_succ_of_accept 111 112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 111 112 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 250 2 55 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 109
  112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 112 250 2 54 56 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 112 250
  (accept_3_3 107 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 112 250 2 53 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 112 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 105 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 112 250 2 52 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 112 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 103 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 112 250 2 51 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 112 250 (accept_3_3 101 112 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 112 250 2 50 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 112 250
  (Polychromatic418967fa.accept_21_15_7_19_1_15090 99 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 112 250 2 49 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 112 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 112 250 2 48 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 112 250 (accept_3_3 95 112 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 112 250 2 47 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 112 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 112 250 2 46 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 112 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 112 250 2 45 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 250 (accept_3_3 89 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 112 250 2 44 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 112 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 250 2 43 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 85 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 250 2 42 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 250 (accept_3_3 83 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 250 2 41 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 250 (Polychromatic418967fa.accept_19_5_17_3_1_4152 81 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 250 2 40 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 250 2 39 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 250 (accept_3_3 77 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 250 2 38 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 250 2 37 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 250 2 36 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 112 250 (accept_3_3 71 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 250 2 35 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 250 2 34 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 112 250 2 33 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 112 250 (accept_3_3 65 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 250 2 32 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 250 (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 250 2 31 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 250 2 30 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 250 (accept_3_3 59 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 250 2 29 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 250 2 28 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 250 2 27 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 250 (accept_3_3 53 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 250 2 26 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 250 2 25 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 250
  (Polychromatic418967fa.accept_11_5_2_8_1_866 49 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 250 2 24 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 250 (accept_3_3 47 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 250 2 23 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 250 (Polychromatic418967fa.accept_20_5_12_10_1_5072 45 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 250 2 22 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 250 2 21 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 250 (accept_3_3 41 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 250 2 20 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 250 2 19 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 250 2 18 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 250 (accept_3_3 35 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 250 2 17 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 250 2 16 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 250 2 15 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 250 (accept_3_3 29 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 250 2 14 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 250 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 250 2 13 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 250 2 12 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 250 (accept_3_3 23 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 250 2 11 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 250 2 10 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 250 2 9 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 250 (accept_3_3 17 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 250 2 8 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 112 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 250 2 7 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 112 250 2 6 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 112 250 (accept_3_3 11 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 250 2 5 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 250 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 112 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 250 2 4 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 250 2 3 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 250 (accept_3_3 5 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  250 2 2 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 250 2 1 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 112 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 250 (allA_succ_of_accept 110 111 250 (accept_3_3 110 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 250 (Polychromatic418967fa.accept_13_4_7_3_1_92 108 111
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 250 (accept_3_3 107 111
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 106 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 250 (accept_3_3 104 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 250 (Polychromatic418967fa.accept_7_4_6_5_1_141
  102 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 250 (accept_3_3
  101 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 100 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 111 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 250 (accept_3_3 98 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 250 (Polychromatic418967fa.accept_9_6_3_7_1_580
  96 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 250 (accept_3_3 95
  111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 94 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 250 (accept_3_3 92 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 250 (Polychromatic418967fa.accept_12_6_3_10_1_224
  90 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 250 (accept_3_3 89
  111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 88 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 111 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 250 (accept_3_3 86 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 250
  (Polychromatic418967fa.accept_20_4_11_10_1_8025 84 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 111 250 (accept_3_3 83 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 250 (accept_3_3 80 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 79
  111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 250 (accept_3_3 77 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 250 (Polychromatic418967fa.accept_13_10_7_3_1_3041 75 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 250 (accept_3_3 74 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 250
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 111 250 (accept_3_3 71 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 250 (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 250 (accept_3_3 68 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 250 (accept_3_3 65 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 250 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 250 (accept_3_3 62 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 250 (accept_3_3 59 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 250 (accept_3_3 56 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 250 (accept_3_3 53 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 250 (Polychromatic418967fa.accept_19_14_16_3_1_15089 52 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 250 (accept_3_3 50 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 250
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 250 (accept_3_3 47 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 250 (accept_3_3 44 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 250 (accept_3_3 41 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 250 (accept_3_3 38 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 250 (accept_3_3 35 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 250 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 250 (accept_3_3 32 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 250 (accept_3_3 29 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 250 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 250 (accept_3_3 26 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 250 (accept_3_3 23 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 250 (accept_3_3 20 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 250 (accept_3_3 17 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 250 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 250 (accept_3_3 14 111 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 250
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 250 (accept_3_3 11 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 250 (accept_3_3 8 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 250 (accept_3_3 5 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 250 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 250 (accept_3_3 2 111 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 250 (allA_of_3_1 110 110 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 250
  (allA_succ_of_accept 108 109 250 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 250 (accept_3_3 107 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 106 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 250 (accept_3_3 104 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 250 (accept_3_3 101 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 109
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 250 (accept_3_3 98 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 250 (accept_3_3 95 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 250 (accept_3_3 92 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 250 (accept_3_3 89 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 250 (accept_3_3 86 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 250 (accept_3_3 83 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 250 (Polychromatic418967fa.accept_15_7_4_10_1_1513 82 109 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 250 (accept_3_3 80 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 250 (accept_3_3 77 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 250 (accept_3_3 74 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 250 (Polychromatic418967fa.accept_13_8_5_3_1_427 73 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 250 (accept_3_3 71 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 250 (Polychromatic418967fa.accept_17_2_7_12_1_1078 70 109 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 250 (accept_3_3 68 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 250 (accept_3_3 65 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 250 (accept_3_3 62 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 250 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 250 (accept_3_3 59 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 250 (accept_3_3 56 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 250 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 250 (accept_3_3 53 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 109
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 250 (accept_3_3 50 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 250 (accept_3_3 47 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 250 (Polychromatic418967fa.accept_16_14_13_10_1_2624 46 109 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 250 (accept_3_3 44 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 250 (accept_3_3 41 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 250 (accept_3_3 38 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 250 (accept_3_3 35 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 250 (accept_3_3 32 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 250 (accept_3_3 29 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 250 (accept_3_3 26 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 250 (Polychromatic418967fa.accept_18_7_1_16_1_578 25 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 250 (accept_3_3 23 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 250 (accept_3_3 20 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 250 (Polychromatic418967fa.accept_19_18_14_3_1_8427 18 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 250 (accept_3_3 17 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 250 (accept_3_3 14 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 250 (accept_3_3 11 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 250 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 109 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 250 (accept_3_3 8 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 250 (accept_3_3 5 109 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 250 (accept_3_3 2 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 250 (allA_succ_of_accept 107 108 250 (accept_3_3 107 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 108 250 2 53 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 108 250 (Polychromatic418967fa.accept_13_1_4_3_1_1545 105 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 250 2 52 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 250
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 103 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 108 250 2 51 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 108 250 (accept_3_3 101 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 108 250 2 50 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 108 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 250 2 49 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 250
  (Polychromatic418967fa.accept_15_7_3_10_1_817 97 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 250 2 48 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 250 (accept_3_3 95 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 250 2 47 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 250 2 46 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 250
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 91 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 108 250 2 45 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 250 (accept_3_3 89 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 250 2 44 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 250 (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 250 2 43 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 85 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 250 2 42 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 250 (accept_3_3 83 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 250 2 41 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 250 (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 250 2 40 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 250 2 39 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 250 (accept_3_3 77 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 250 2 38 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 250 (Polychromatic418967fa.accept_14_5_10_12_1_1454 75 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 250 2 37 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 250
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 73 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 108 250 2 36 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 108 250 (accept_3_3 71 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 250 2 35 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 250 (Polychromatic418967fa.accept_15_9_3_10_1_2312 69 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 250 2 34 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 250
  (Polychromatic418967fa.accept_15_7_3_10_1_817 67 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 250 2 33 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 250 (accept_3_3 65 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 250 2 32 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 250 (Polychromatic418967fa.accept_22_19_20_8_1_8920 63 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 250 2 31 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 250
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 61 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 250 2 30 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 250 (accept_3_3 59 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 250 2 29 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 250 2 28 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 250
  (Polychromatic418967fa.accept_20_15_8_10_1_3602 55 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 108 250 2 27 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 108 250 (accept_3_3 53 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 250 2 26 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 250 2 25 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 250
  (Polychromatic418967fa.accept_19_11_13_3_1_9820 49 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 250 2 24 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 250 (accept_3_3 47 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 250 2 23 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 250 (Polychromatic418967fa.accept_16_13_12_10_1_3540 45 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 250 2 22 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 250 2 21 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 250 (accept_3_3 41 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 250 2 20 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 250 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 250 2 19 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 250 2 18 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 250 (accept_3_3 35 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 250 2 17 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 250 2 16 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 250
  (Polychromatic418967fa.accept_19_12_13_3_1_5447 31 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 250 2 15 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 250 (accept_3_3 29 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 250 2 14 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 250 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 250 2 13 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 250
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 250 2 12 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 250 (accept_3_3 23 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 250 2 11 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 250 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 250 2 10 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 250
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 19 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 108 250 2 9 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 108 250 (accept_3_3 17 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 250 2 8 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 108 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 250 2 7 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 250
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 250 2 6 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 250 (accept_3_3 11 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 250 2 5 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 250 2 4 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 250
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 250 2 3 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 250 (accept_3_3 5 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108
  250 2 2 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  108 250 (Polychromatic418967fa.accept_16_3_12_10_1_315 3 108 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 108 250 2 1 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 108 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 250 (allA_of_3_1 107 107 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 250
  (allA_succ_of_accept 105 106 250 (Polychromatic418967fa.accept_13_1_2_3_1_911 105 106 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 250 2 52 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  103 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 106 250 2 51 53 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 106 250
  (accept_3_3 101 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 106 250 2 50 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 106 250
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 99 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 106 250 2 49 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 106 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 106 250 2 48 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 106 250 (accept_3_3 95 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 106 250 2 47 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 106 250 (Polychromatic418967fa.accept_17_8_4_12_1_1994
  93 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 250 2 46 53 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 250
  (Polychromatic418967fa.accept_21_7_1_19_1_6021 91 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 250 2 45 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 250 (accept_3_3 89 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 250 2 44 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 250 2 43 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 250
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 85 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 250 2 42 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 250 (accept_3_3 83 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 250 2 41 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 250 2 40 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 250
  (Polychromatic418967fa.accept_13_1_2_3_1_911 79 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 250 2 39 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 250 (accept_3_3 77 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 250 2 38 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 250 (Polychromatic418967fa.accept_13_10_2_3_1_3025 75 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 250 2 37 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 73 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 250 2 36 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 250 (accept_3_3 71 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 250 2 35 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 250 2 34 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 250 2 33 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 250 (accept_3_3 65 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 250 2 32 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 250 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 250 2 31 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 250
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 61 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 250 2 30 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 250 (accept_3_3 59 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 250 2 29 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 250 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 250 2 28 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 250 2 27 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 250 (accept_3_3 53 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 250 2 26 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 250 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 250 2 25 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 250
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 250 2 24 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 250 (accept_3_3 47 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 250 2 23 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 250 2 22 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 250
  (Polychromatic418967fa.accept_15_13_1_10_1_816 43 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 250 2 21 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 250 (accept_3_3 41 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 250 2 20 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 250 2 19 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 250
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 250 2 18 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 250 (accept_3_3 35 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 250 2 17 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 250 (Polychromatic418967fa.accept_19_14_11_3_1_5508 33 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 250 2 16 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 250 2 15 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 250 (accept_3_3 29 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 250 2 14 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 250 2 13 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 250 2 12 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 250 (accept_3_3 23 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 250 2 11 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 250 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 250 2 10 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 250
  (Polychromatic418967fa.accept_17_2_4_12_1_6587 19 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 250 2 9 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 250 (accept_3_3 17 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 250 2 8 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 250 2 7 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 250 2 6 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 250 (accept_3_3 11 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 250 2 5 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 250 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 106 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 250 2 4 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 250
  (Polychromatic418967fa.accept_15_7_1_10_1_305 7 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 250 2 3 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 250 (accept_3_3 5 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  250 2 2 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 106 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 250 2 1 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 250 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 106 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 250 (allA_succ_of_accept 104 105 250 (accept_3_3 104 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 250 (accept_3_3 101 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 250 5 20 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 105 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 105 250 (accept_3_3 98 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 105 250 (Polychromatic418967fa.accept_13_5_1_3_1_878 96 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 250 5 19 21 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 94 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 250 (accept_3_3 92 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 250 5 18 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 250 (accept_3_3 89 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 250 (Polychromatic418967fa.accept_19_12_10_3_1_5503 88 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 105 250 (accept_3_3 86 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  105 250 5 17 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 250 (accept_3_3 83 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 105 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 250
  (Polychromatic418967fa.accept_16_1_9_10_1_4740 81 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 105 250 5 16 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 250 (Polychromatic418967fa.accept_12_6_9_10_1_565
  78 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 250 (accept_3_3 77
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 76 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 250 5 15 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 250 (accept_3_3 74 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 250 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 250 (accept_3_3 71 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 250 5 14 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 250
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 250 (accept_3_3 68 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 250 5 13 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 250 (accept_3_3 62 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 250 5 12 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 250 (accept_3_3 59 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 105 250 (accept_3_3 56 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  105 250 5 11 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 105 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 250 (accept_3_3 53 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 105 250 (Polychromatic418967fa.accept_20_12_5_10_1_9540 52 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 105 250 5 10 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 250 (accept_3_3 47
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 250 5 9 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 105 250 (accept_3_3 44 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 250 (accept_3_3 41 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 250 5 8 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 250 (accept_3_3 38
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 250
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 105 250 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 250 5 7 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 250
  (Polychromatic418967fa.accept_19_15_10_3_1_12550 34 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 250 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 250 (accept_3_3 32 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 250 5 6 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 250 (accept_3_3 29
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 250 (accept_3_3 26 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 105 250 5 5 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 105 250 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 250 (accept_3_3 23 105 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 105 250 5 4 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 250 (accept_3_3 17 105
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 250
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 250 5 3 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 250 (accept_3_3 14 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 250 (accept_3_3 11 105 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 250 5 2 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 250 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 250 (accept_3_3 8 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 105 250 5 1 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 250 (accept_3_3 2 105 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  105 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 250 (allA_of_3_1 104 104 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 250
  (allA_succ_of_accept 102 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 103 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 250 (accept_3_3 101 103 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 99
  103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 103 250 (accept_3_3 98
  103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 103 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 250 (accept_3_3 95 103 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 103 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 94 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 250 (accept_3_3 92 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 250 (Polychromatic418967fa.accept_19_14_8_3_1_6981 90 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 250 (accept_3_3 89 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 103
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 250 (accept_3_3 86 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 250 (accept_3_3 83 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 250 (accept_3_3 80 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 250 (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 250 (accept_3_3 77 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 250 (accept_3_3 74 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 250 (Polychromatic418967fa.accept_15_12_13_10_1_812 72 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 250 (accept_3_3 71 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 250 (Polychromatic418967fa.accept_19_13_8_3_1_2906 70 103
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 250 (accept_3_3 68 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 250 (accept_3_3 65 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 250 (accept_3_3 62 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 250 (accept_3_3 59 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 250 (Polychromatic418967fa.accept_23_12_11_20_1_15088 58 103 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 250 (accept_3_3 56 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 250 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 250 (accept_3_3 53 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 103
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 250 (accept_3_3 50 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 250 (accept_3_3 47 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 250 (accept_3_3 44 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 250 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 250 (accept_3_3 41 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 250 (accept_3_3 38 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 250 (Polychromatic418967fa.accept_19_17_8_3_1_11211 36 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 250 (accept_3_3 35 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 103
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 250 (accept_3_3 32 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 250 (Polychromatic418967fa.accept_14_3_5_12_1_4000 31 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 250 (accept_3_3 29 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 250 (accept_3_3 26 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 250 (accept_3_3 23 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 250 (Polychromatic418967fa.accept_13_9_12_3_1_907 22 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 250 (accept_3_3 20 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 250 (accept_3_3 17 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 103
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 250 (accept_3_3 14 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 250 (accept_3_3 11 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 250 (accept_3_3 8 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 250 (accept_3_3 5 103 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 250 (accept_3_3 2 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 250 (allA_succ_of_accept 101 102 250 (accept_3_3 101 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 250 2 50 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 250 2 49 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 97 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 250 2 48 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 250 (accept_3_3 95 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 250 2 47 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 250 2 46 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 250 2 45 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 250 (accept_3_3 89 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 250 2 44 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 250 2 43 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 85 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 250 2 42 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 250 (accept_3_3 83 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 250 2 41 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 250 2 40 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 79 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 250 2 39 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 250 (accept_3_3 77 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 250 2 38 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 250 2 37 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 250 2 36 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 250 (accept_3_3 71 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 250 2 35 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 250 2 34 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 250 2 33 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 250 (accept_3_3 65 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 250 2 32 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 250 2 31 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 250
  (Polychromatic418967fa.accept_11_6_3_8_1_843 61 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 250 2 30 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 250 (accept_3_3 59 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 250 2 29 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 250 2 28 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 250 2 27 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 250 (accept_3_3 53 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 250 2 26 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 250 2 25 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 250 2 24 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 250 (accept_3_3 47 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 250 2 23 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 250 2 22 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 250 2 21 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 250 (accept_3_3 41 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 250 2 20 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 250 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 250 2 19 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 250 2 18 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 250 (accept_3_3 35 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 250 2 17 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 250 2 16 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 250 2 15 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 250 (accept_3_3 29 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 250 2 14 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 250 2 13 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 250
  (Polychromatic418967fa.accept_19_6_7_3_1_1733 25 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 250 2 12 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 250 (accept_3_3 23 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 250 2 11 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 250 2 10 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 250 2 9 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 250 (accept_3_3 17 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 250 2 8 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 250 2 7 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 250 2 6 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 250 (accept_3_3 11 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 250 2 5 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 250 2 4 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 250
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 250 2 3 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 250 (accept_3_3 5 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  250 2 2 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 250 2 1 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 102 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 250 (allA_of_3_1 101 101 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 250 (allA_succ_of_accept 99
  100 250 (Polychromatic418967fa.accept_13_8_9_3_1_2213 99 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 250 2 49 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 250 2 48 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 100 250 5 19 20 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 100 250 2 47 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 93 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 250 2 46 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 250 10 9 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 250 (accept_3_3 89 100 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 250 2 44 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 250 2 43 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 100 250 5 17 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 100 250 2 42 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 250 (accept_3_3 83 100 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 100 250 2 41 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 100 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 250 10 8 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 250 2 39 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 250 (accept_3_3 77 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 250 2 38 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 100 250 25 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 100 250 2 37 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 100 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 100 250 2 36 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 100 250 (accept_3_3 71 100 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 250 10 7 10 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 100 250 2 34 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 100 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 100 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 100 250 2 33 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 100 250 5 13 20 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 100 250 2 32 50 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 100 250
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 100 250 2 31 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 100 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 250 10 6 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 250 (accept_3_3 59 100 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 100 250 2 29 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 100 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 100 250 2 28 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 100 250 5 11 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 100 250 2 27 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 100 250 (accept_3_3 53 100 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 100 250 2 26 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 100 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 250 50 1 2 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 250 2 24 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 250 (accept_3_3 47 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 250 2 23 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 100 250 5 9 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 250 2 22 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 250 2 21 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 250 (accept_3_3 41 100 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 250 10 4 10 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 250 2 19 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 250 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 250 2 18 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 100 250 5 7 20 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 100 250 2 17 50 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 250 2 16 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 100 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 250 10 3 10 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 250 (accept_3_3 29 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 250 2 14 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 250 (Polychromatic418967fa.accept_19_8_5_3_1_4181
  27 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 250 2 13 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 250 25 1 4 10
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 250 2 12 50
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 250
  (accept_3_3 23 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 250 2 11 50 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 250 10 2 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 250 2 9 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 250 (accept_3_3 17 100 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 250 2 8 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 100 250 5 3 20 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 250 2 7 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 250 2 6 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 100 250 (accept_3_3 11 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 250 10 1 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 250 (Polychromatic418967fa.accept_23_9_8_20_1_13574 9 100 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 250 2 4 50 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 250 2 3 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 100 250 5 1 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 100 250 2 2 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 100 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 250 2 1 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  100 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  250 (allA_succ_of_accept 98 99 250 (accept_3_3 98 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 250 (Polychromatic418967fa.accept_13_5_8_3_1_1535 96 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 250 (accept_3_3 95 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 250 (accept_3_3 92 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 250 (accept_3_3 89 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 250 (accept_3_3 86 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 250 (Polychromatic418967fa.accept_18_12_9_16_1_4732 84 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 250 (accept_3_3 83 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 250 (Polychromatic418967fa.accept_19_6_4_3_1_11188 82 99
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 250 (accept_3_3 80 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 78 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 250 (accept_3_3 77 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 250
  (Polychromatic418967fa.accept_19_18_4_3_1_4140 75 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 250 (accept_3_3 74 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 250 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 250 (accept_3_3 71 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 250 (Polychromatic418967fa.accept_13_5_8_3_1_1535 70 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 250 (accept_3_3 68 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 250 (accept_3_3 65 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 250 (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 250
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 250 (accept_3_3 62 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 250 (accept_3_3 59 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 250 (Polychromatic418967fa.accept_19_1_4_3_1_8404 58 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 250 (accept_3_3 56 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 250 (accept_3_3 53 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 250
  (Polychromatic418967fa.accept_18_15_9_16_1_6029 51 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 250 (accept_3_3 50 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 250 (accept_3_3 47 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 250 (accept_3_3 44 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 250 (accept_3_3 41 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 250 (Polychromatic418967fa.accept_24_16_3_10_1_11774 40 99 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 250 (accept_3_3 38 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 250 (Polychromatic418967fa.accept_20_16_19_10_1_12352 36 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 250 (accept_3_3 35 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 99 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 250 (accept_3_3 32 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 250 (accept_3_3 29 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 250 (Polychromatic418967fa.accept_16_12_3_10_1_3524 28 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 250 (accept_3_3 26 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 250 (accept_3_3 23 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 250 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 250 (accept_3_3 20 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 250 (accept_3_3 17 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 250 (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 99 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 250
  (Polychromatic418967fa.accept_17_15_14_12_1_1973 15 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 250 (accept_3_3 14 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 250 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 99
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 250 (accept_3_3 11 99 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 10
  99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 250 (accept_3_3 8 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 250 (accept_3_3 5 99 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 250 (accept_3_3 2 99 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  250 (allA_of_3_1 98 98 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 250 (allA_succ_of_accept 96 97 250
  (Polychromatic418967fa.accept_13_5_6_3_1_868 96 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 250 (accept_3_3 95 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 250 (Polychromatic418967fa.accept_15_4_7_10_1_807 94 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 250 (accept_3_3 92 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 250
  (Polychromatic418967fa.accept_14_6_13_12_1_810 90 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 250 (accept_3_3 89 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 250 (accept_3_3 86 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 250
  (Polychromatic418967fa.accept_22_18_9_8_1_1365 84 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 250 (accept_3_3 83 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 250 (Polychromatic418967fa.accept_19_6_2_3_1_11217 82 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 250 (accept_3_3 80 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 250 (accept_3_3 77 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 250 (Polychromatic418967fa.accept_11_10_9_8_1_1974 76 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 250 (accept_3_3 74 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 250 (Polychromatic418967fa.accept_16_9_1_10_1_3610 73 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 250
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 250 (accept_3_3 71 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 250 (Polychromatic418967fa.accept_13_5_6_3_1_868 70 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 250 (accept_3_3 68 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 250
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 66 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 250 (accept_3_3 65 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 250 (accept_3_3 62 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 250 (Polychromatic418967fa.accept_13_9_6_3_1_1514 61 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 250 (accept_3_3 59 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 250 (Polychromatic418967fa.accept_18_4_7_16_1_2307 58 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 250 (accept_3_3 56 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 250
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 250 (accept_3_3 53 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 250 (accept_3_3 50 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 250 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 250
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 250 (accept_3_3 47 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 250 (accept_3_3 44 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 250
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 250 (accept_3_3 41 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 250 (accept_3_3 38 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 250 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 250 (accept_3_3 35 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 250 (Polychromatic418967fa.accept_14_6_13_12_1_810 34 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 250 (accept_3_3 32 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 250
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 30 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 250 (accept_3_3 29 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 250 (accept_3_3 26 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 250
  (Polychromatic418967fa.accept_19_5_2_3_1_5527 24 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 250 (accept_3_3 23 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 250 (accept_3_3 20 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 250 (accept_3_3 17 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 250 (accept_3_3 14 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 250 (Polychromatic418967fa.accept_20_13_17_10_1_3631 13 97 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 250
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 250 (accept_3_3 11 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 250 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 250 (accept_3_3 8 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 250
  (Polychromatic418967fa.accept_14_6_13_12_1_810 6 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 250 (accept_3_3 5 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 250 (accept_3_3 2 97 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 250
  (allA_succ_of_accept 95 96 250 (accept_3_3 95 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  250 2 47 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 250 2 46 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 250 2 45 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 250 (accept_3_3 89 96 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 250 2 44 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 250
  (Polychromatic418967fa.accept_13_9_5_3_1_428 87 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 250 2 43 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 250 2 42 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 250 (accept_3_3 83 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 250 2 41 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 250
  (Polychromatic418967fa.accept_17_13_11_12_1_4131 81 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 96 250 2 40 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 96 250 (Polychromatic418967fa.accept_13_1_5_3_1_888 79 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 250 2 39 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 250 (accept_3_3 77 96 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 250 2 38 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 250 2 37 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 250 2 36 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 250 (accept_3_3 71 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 250 2 35 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 250 (Polychromatic418967fa.accept_18_15_6_16_1_4730
  69 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 250 2 34 48 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 250 2 33 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 250 (accept_3_3 65 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 250 2 32 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 250 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 250 2 31 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 250
  (Polychromatic418967fa.accept_13_9_5_3_1_428 61 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 250 2 30 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 250 (accept_3_3 59 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 250 2 29 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 250 2 28 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 250 2 27 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 250 (accept_3_3 53 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 250 2 26 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 96 250 (Polychromatic418967fa.accept_18_15_6_16_1_4730 51 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 250 2 25 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 250 2 24 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 250 (accept_3_3 47 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 250 2 23 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 96 250 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 250 2 22 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 250
  (Polychromatic418967fa.accept_19_5_1_3_1_8421 43 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 250 2 21 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 250 (accept_3_3 41 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 250 2 20 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 250 2 19 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 250 2 18 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 250 (accept_3_3 35 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 250 2 17 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 96 250 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 250 2 16 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 250 2 15 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 250 (accept_3_3 29 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 250 2 14 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 250 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 250 2 13 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 250
  (Polychromatic418967fa.accept_19_6_1_3_1_11225 25 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 250 2 12 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 250 (accept_3_3 23 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 250 2 11 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 96 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 250 2 10 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 250 2 9 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 250 (accept_3_3 17 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96
  250 2 8 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  96 250 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 250 2 7 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 96 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 250 2 6 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 250 (accept_3_3 11 96 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 250 2 5 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 250
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 96 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 250 2 4 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 250 (Polychromatic418967fa.accept_21_7_12_19_1_10712 7 96 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 250 2 3 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 250 (accept_3_3 5 96 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 250 2 2 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 250 2 1 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 250
  (allA_of_3_1 95 95 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 250 (allA_succ_of_accept 93 94 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 94 250 2 46 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 94 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 250 2 45 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 250 (accept_3_3 89 94 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 250 2 44 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 94 250 2 43 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 94 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 85 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 94 250 2 42 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 94 250 (accept_3_3 83 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 94 250 2 41 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 94 250 (Polychromatic418967fa.accept_15_6_4_10_1_2319 81 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 250 2 40 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 250 2 39 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 250 (accept_3_3 77 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 250 2 38 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 250 2 37 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 250 2 36 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 250 (accept_3_3 71 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 250 2 35 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 250 2 34 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 250
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 250 2 33 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 250 (accept_3_3 65 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 250 2 32 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 250 (Polychromatic418967fa.accept_16_15_14_10_1_9549 63 94 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 250 2 31 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 250
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 61 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 250 2 30 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 250 (accept_3_3 59 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 250 2 29 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 250 2 28 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 250 2 27 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 250 (accept_3_3 53 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 250 2 26 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 250 2 25 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 250
  (Polychromatic418967fa.accept_19_11_18_3_1_1755 49 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 250 2 24 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 250 (accept_3_3 47 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 250 2 23 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 250 (Polychromatic418967fa.accept_16_13_14_10_1_1669 45 94 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 250 2 22 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 250 2 21 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 250 (accept_3_3 41 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 250 2 20 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 250 2 19 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 250 2 18 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 250 (accept_3_3 35 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 250 2 17 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 250 2 16 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 250
  (Polychromatic418967fa.accept_16_15_14_10_1_9549 31 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 94 250 2 15 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 94 250 (accept_3_3 29 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 250 2 14 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 250 (Polychromatic418967fa.accept_28_27_10_26_1_15087 27 94 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 250 2 13 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 250
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 250 2 12 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 250 (accept_3_3 23 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 250 2 11 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 250 2 10 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 250 2 9 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 250 (accept_3_3 17 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  250 2 8 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 250 2 7 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 250 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 94 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 250 2 6 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 250 (accept_3_3 11 94 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 250 2 5 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 250 2 4 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 250 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 94 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 250 2 3 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 250 (accept_3_3 5 94 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 250 2 2 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 250 2 1 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 250
  (allA_succ_of_accept 92 93 250 (accept_3_3 92 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 250 (accept_3_3 89 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 250 (accept_3_3 86 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 250 (Polychromatic418967fa.accept_15_9_3_10_1_2312 84 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 250 (accept_3_3 83 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 93 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 250 (accept_3_3 80 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 250 (accept_3_3 77 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 250 (accept_3_3 74 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 250 (Polychromatic418967fa.accept_17_4_8_12_1_9165 72 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 250 (accept_3_3 71 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 250 (Polychromatic418967fa.accept_13_5_2_3_1_1526 70 93 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 250 (accept_3_3 68 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 250 (accept_3_3 65 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 250 (accept_3_3 62 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 250 (accept_3_3 59 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 250
  (Polychromatic418967fa.accept_11_2_5_8_1_470 57 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 250 (accept_3_3 56 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 250 (accept_3_3 53 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 250 (accept_3_3 50 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 250 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 250 (accept_3_3 47 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 250 (accept_3_3 44 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 250 (accept_3_3 41 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 250 (accept_3_3 38 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 250 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 250 (accept_3_3 35 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 250 (Polychromatic418967fa.accept_19_15_17_3_1_13760 34 93 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 250 (accept_3_3 32 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 250 (accept_3_3 29 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 250 (accept_3_3 26 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 250 (accept_3_3 23 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 250
  (Polychromatic418967fa.accept_14_7_9_12_1_3975 21 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 250 (accept_3_3 20 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 250 (accept_3_3 17 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 250 (Polychromatic418967fa.accept_19_16_17_3_1_2916 16 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 250 (accept_3_3 14 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 250 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 250 (accept_3_3 11 93 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 250
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 250 (accept_3_3 8 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 250 (accept_3_3 5 93 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 250 (accept_3_3 2 93 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 250
  (allA_of_3_1 92 92 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 250 (allA_succ_of_accept 90 91 250
  (Polychromatic418967fa.accept_23_21_22_20_1_8631 90 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 91 250 (accept_3_3 89 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 91 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 91 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 250 (accept_3_3 86 91 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 250 (accept_3_3 83 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 250 (Polychromatic418967fa.accept_11_5_3_8_1_454 82 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 250 (accept_3_3 80 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 250 (Polychromatic418967fa.accept_14_9_7_12_1_4034 79 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 250 (accept_3_3 77 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 250 (accept_3_3 74 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 250
  (Polychromatic418967fa.accept_11_6_3_8_1_843 72 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 250 (accept_3_3 71 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 250 (Polychromatic418967fa.accept_17_2_6_12_1_7912 70 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 250 (accept_3_3 68 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 250 (accept_3_3 65 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 250 (accept_3_3 62 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 250 (accept_3_3 59 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 250 (accept_3_3 56 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 250 (Polychromatic418967fa.accept_19_17_15_3_1_4174 55 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 250
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 250 (accept_3_3 53 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 250 (accept_3_3 50 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 250 (accept_3_3 47 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 250 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 250 (accept_3_3 44 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 250 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 250 (accept_3_3 41 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 250 (accept_3_3 38 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 250
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 250 (accept_3_3 35 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 250 (Polychromatic418967fa.accept_20_14_11_10_1_11036 34 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 250 (accept_3_3 32 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 250 (accept_3_3 29 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 250 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 250 (accept_3_3 26 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 250 (accept_3_3 23 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 250 (accept_3_3 20 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 250 (Polychromatic418967fa.accept_14_5_7_12_1_4006 19 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 250
  (Polychromatic418967fa.accept_17_1_6_12_1_1944 18 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 250 (accept_3_3 17 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 250 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 250 (accept_3_3 14 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 250 (accept_3_3 11 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 250 (Polychromatic418967fa.accept_17_10_6_12_1_11635 10 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 250 (accept_3_3 8 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 91 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 250 (accept_3_3 5 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 250 (accept_3_3 2 91 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 250
  (allA_succ_of_accept 89 90 250 (accept_3_3 89 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  250 2 44 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 87 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 250 2 43 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 90 250 5 17 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 90 250 2 42 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 250 (accept_3_3 83 90 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 90 250 2 41 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 90 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 250 10 8 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 250
  (Polychromatic418967fa.accept_22_13_2_8_1_15086 79 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 250 2 39 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 250 (accept_3_3 77 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 90 250 2 38 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 90 250 5 15 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 90 250 2 37 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 90 250 (Polychromatic418967fa.accept_19_16_14_3_1_11194 73 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 250 2 36 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 250 (accept_3_3 71 90 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 250 10 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  69 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 250 2 34 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 250 2 33 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 90 250 5 13 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 90 250 2 32 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 90 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 250 2 31 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 250
  (Polychromatic418967fa.accept_13_9_12_3_1_907 61 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 250 10 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 250 (accept_3_3 59 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90
  250 2 29 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 90 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 90 250 2 28 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 250 5 11 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 250 2 27 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 250 (accept_3_3 53 90 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 90 250 2 26 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 90 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 250 10 5 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 250
  (Polychromatic418967fa.accept_11_5_2_8_1_866 49 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 250 2 24 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 250 (accept_3_3 47 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 250 2 23 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 90 250 5 9 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 90 250 2 22 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 90 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 250 2 21 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 250 (accept_3_3 41 90 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 250 10 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 39
  90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 250 2 19 45 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 250
  (Polychromatic418967fa.accept_19_18_14_3_1_8427 37 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 250 2 18 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 90 250 5 7 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 90 250 2 17 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 250 2 16 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 250
  (Polychromatic418967fa.accept_24_7_18_10_1_15085 31 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 90 250 10 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 250 (accept_3_3 29 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 250 2 14 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 90 250 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 250 2 13 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 250 5 5 18 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 250 2 12 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 250 (accept_3_3 23 90 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 250 2 11 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 250
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 250 10 2 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 250 (Polychromatic418967fa.accept_24_19_18_10_1_8351 19 90 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 250 2 9 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 250 (accept_3_3 17 90 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 250 2 8 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 250 5 3 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 250 2 7 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 250 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 90
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 250 2 6 45 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 250 (accept_3_3 11
  90 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 250 10 1 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 250
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 250 2 4 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 250 (Polychromatic418967fa.accept_17_7_5_12_1_1997 7 90 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 250 2 3 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 250 5 1 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 250 2 2 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 250 2 1 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 250 (allA_of_3_1 89 89 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 250 (allA_succ_of_accept 87 88
  250 (Polychromatic418967fa.accept_15_12_13_10_1_812 87 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 88 250 2 43 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 88 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 88 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 250 2 42 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 250 (accept_3_3 83 88 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 250 2 41 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 250
  (Polychromatic418967fa.accept_21_18_4_19_1_1838 81 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 88 250 2 40 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 88 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 250 2 39 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 88 250 (accept_3_3 77 88 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88 250 2 38 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 250 (Polychromatic418967fa.accept_17_7_3_12_1_4098
  75 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 250 2 37 44 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 250 2 36 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 88 250 (accept_3_3 71 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 88 250 2 35 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 88 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 250 2 34 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 250 2 33 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 88 250 (accept_3_3 65 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 88 250 2 32 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 88 250 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 88 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 250 2 31 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 250 2 30 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 88 250 (accept_3_3 59 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 88 250 2 29 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 88 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 250 2 28 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 250 2 27 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 250 (accept_3_3 53 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 250 2 26 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 88 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 250 2 25 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 250 2 24 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 88 250 (accept_3_3 47 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 250 2 23 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 88 250 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 250 2 22 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 250 2 21 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 88 250 (accept_3_3 41 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 88 250 2 20 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 88 250 (Polychromatic418967fa.accept_21_18_4_19_1_1838 39 88 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 250 2 19 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 250 2 18 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 88 250 (accept_3_3 35 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 88 250 2 17 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 88 250 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 250 2 16 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 250 2 15 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 88 250 (accept_3_3 29 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 250 2 14 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 88 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 250 2 13 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 250 2 12 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 88 250 (accept_3_3 23 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 88 250 2 11 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 88 250 (Polychromatic418967fa.accept_19_2_12_3_1_5446 21 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 250 2 10 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 250 2 9 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 250 (accept_3_3 17 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  250 2 8 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 250 2 7 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 88 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 250 2 6 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 250 (accept_3_3 11 88 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 250 2 5 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 250 2 4 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 250 2 3 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 250 (accept_3_3 5 88 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 250 2 2 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 250 (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 88 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 250 2 1 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 250
  (allA_succ_of_accept 86 87 250 (accept_3_3 86 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 250 (accept_3_3 83 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 250 (accept_3_3 80 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 250 (accept_3_3 77 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 250 (accept_3_3 74 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 250 (accept_3_3 71 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 250 (Polychromatic418967fa.accept_13_5_9_3_1_870 70 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 250 (accept_3_3 68 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 250 (accept_3_3 65 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 250
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 63 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 250 (accept_3_3 62 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 250 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 250 (accept_3_3 59 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 250 (accept_3_3 56 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 250 (accept_3_3 53 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 250 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 250 (accept_3_3 50 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 250 (accept_3_3 47 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 250 (accept_3_3 44 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 250 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 250 (accept_3_3 41 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 250 (accept_3_3 38 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 250 (accept_3_3 35 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 250 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 250 (accept_3_3 32 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 250 (accept_3_3 29 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 250
  (Polychromatic418967fa.accept_17_10_2_12_1_1070 27 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 250 (accept_3_3 26 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 250 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 250 (accept_3_3 23 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 87 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 250 (accept_3_3 20 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 250 (accept_3_3 17 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 250 (accept_3_3 14 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 250 (accept_3_3 11 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 250 (accept_3_3 8 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 250 (accept_3_3 5 87 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  87 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 250 (accept_3_3 2 87 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 250
  (allA_of_3_1 86 86 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 250 (allA_succ_of_accept 84 85 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 250 (accept_3_3 83 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 250 5 16 17 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 250 (accept_3_3 77 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 250 5 15 17 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 250 (accept_3_3 74 85 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 250
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 72 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 250 (accept_3_3 71 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  250 5 14 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 250 (accept_3_3 68 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 85 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 250 5 13 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 250 (accept_3_3 62 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 250 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 250 5 12 17 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 250 (accept_3_3 59 85 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 250 (Polychromatic418967fa.accept_20_18_5_10_1_3533 58 85
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 250 (accept_3_3 56 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  250 5 11 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 250 (Polychromatic418967fa.accept_20_14_5_10_1_3647 54 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 250 (accept_3_3 53 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 250 5 10 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 250
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 250 (accept_3_3 47 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 250 5 9 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 250 (accept_3_3 44 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 250 (accept_3_3 41 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  250 5 8 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 250 (accept_3_3 38 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 250 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 85
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 250 5 7 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 250 (accept_3_3 32 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 250 5 6 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 250 (accept_3_3 29 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 250 (accept_3_3 26 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  250 5 5 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 250 (accept_3_3 23 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 250 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 250 5 4 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 250 (accept_3_3 17 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 250 5 3 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 250 (accept_3_3 14 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 250 (accept_3_3 11 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  250 5 2 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 250 (accept_3_3 8 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 250 5 1 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 250 (accept_3_3 2 85 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 250
  (allA_succ_of_accept 83 84 250 (accept_3_3 83 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  250 2 41 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 250 2 40 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 250 (Polychromatic418967fa.accept_13_1_6_3_1_1547 79 84 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 250 2 39 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 250 (accept_3_3 77 84 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 250 2 38 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 250
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 75 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 250 2 37 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 250 2 36 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 250 (accept_3_3 71 84 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 250 2 35 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 250 2 34 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 250 2 33 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 250 (accept_3_3 65 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 250 2 32 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 84 250 (Polychromatic418967fa.accept_15_3_9_10_1_2325 63 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 250 2 31 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 250
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 61 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 250 2 30 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 250 (accept_3_3 59 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 250 2 29 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 84 250 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 250 2 28 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 250 2 27 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 250 (accept_3_3 53 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 250 2 26 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 84 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 250 2 25 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 250 2 24 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 250 (accept_3_3 47 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 250 2 23 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 250 (Polychromatic418967fa.accept_17_11_16_12_1_1984 45 84 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 250 2 22 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 250
  (Polychromatic418967fa.accept_19_5_8_3_1_5498 43 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 250 2 21 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 250 (accept_3_3 41 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 250 2 20 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 84 250 (Polychromatic418967fa.accept_27_12_3_7_1_15084 39 84 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 250 2 19 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 250 2 18 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 250 (accept_3_3 35 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 250 2 17 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 84 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 250 2 16 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 250 2 15 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 250 (accept_3_3 29 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 250 2 14 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 250 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 250 2 13 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 250
  (Polychromatic418967fa.accept_19_6_8_3_1_11219 25 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 250 2 12 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 250 (accept_3_3 23 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 250 2 11 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 84 250 (Polychromatic418967fa.accept_20_1_4_10_1_3645 21 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 250 2 10 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 250 2 9 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 250 (accept_3_3 17 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  250 2 8 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 250 2 7 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 84 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 250 2 6 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 250 (accept_3_3 11 84 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 250 2 5 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 250
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 250 2 4 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 250 (Polychromatic418967fa.accept_22_7_18_8_1_13589 7 84 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 250 2 3 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 250 (accept_3_3 5 84 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 250 2 2 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 250 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 250 2 1 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 250 (allA_of_3_1
  83 83 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 250 (allA_succ_of_accept 81 82 250
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 81 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 250 2 40 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 79 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 250 2 39 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 250 (accept_3_3 77 82 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 250 2 38 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 75
  82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 250 2 37 41 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 250
  (Polychromatic418967fa.accept_18_1_10_16_1_566 73 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 250 2 36 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 250 (accept_3_3 71 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 250 2 35 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 250 2 34 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 250 2 33 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 250 (accept_3_3 65 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 250 2 32 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 250 (Polychromatic418967fa.accept_15_3_7_10_1_2324 63 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 250 2 31 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 250
  (Polychromatic418967fa.accept_15_1_7_10_1_287 61 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 250 2 30 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 250 (accept_3_3 59 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 250 2 29 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 250 2 28 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 250
  (Polychromatic418967fa.accept_18_1_10_16_1_566 55 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 250 2 27 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 250 (accept_3_3 53 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 250 2 26 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 250 2 25 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 250 2 24 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 250 (accept_3_3 47 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 250 2 23 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 250 (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 82 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 250 2 22 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 250
  (Polychromatic418967fa.accept_17_9_14_12_1_9177 43 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 250 2 21 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 250 (accept_3_3 41 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 250 2 20 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 250 2 19 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 250
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 250 2 18 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 250 (accept_3_3 35 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 250 2 17 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 250 2 16 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 250 2 15 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 250 (accept_3_3 29 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 250 2 14 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 250 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 250 2 13 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 250
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 250 2 12 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 250 (accept_3_3 23 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 250 2 11 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 250 2 10 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 250
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 250 2 9 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 250 (accept_3_3 17 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  250 2 8 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 250 2 7 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 250 2 6 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 250 (accept_3_3 11 82 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 250 2 5 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 250
  (Polychromatic418967fa.accept_17_9_14_12_1_9177 9 82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 250 2 4 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 82 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 250 2 3 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 250 (accept_3_3 5 82 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 250 2 2 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 250 2 1 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 250 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1
  82 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 250
  (allA_succ_of_accept 80 81 250 (accept_3_3 80 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 250 (accept_3_3 77 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 250 (accept_3_3 74 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 250 (accept_3_3 71 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 250 (Polychromatic418967fa.accept_21_7_18_19_1_10715 70 81 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 250 (accept_3_3 68 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 250 (accept_3_3 65 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 250 (accept_3_3 62 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 250 (Polychromatic418967fa.accept_31_29_19_2_1_15083 60 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 250 (accept_3_3 59 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 81 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 250 (accept_3_3 56 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 250 (accept_3_3 53 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 250 (Polychromatic418967fa.accept_17_1_13_12_1_1084 52 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 250 (accept_3_3 50 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 250 (accept_3_3 47 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 250 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 250
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 250 (accept_3_3 44 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 250 (accept_3_3 41 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 250 (accept_3_3 38 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 250 (accept_3_3 35 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 250
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 250 (accept_3_3 32 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 250 (accept_3_3 29 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 250 (Polychromatic418967fa.accept_17_11_13_12_1_1968 28 81 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 250 (accept_3_3 26 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 250 (Polychromatic418967fa.accept_20_4_1_10_1_3643 24 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 250 (accept_3_3 23 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 250
  (Polychromatic418967fa.accept_19_2_5_3_1_5536 21 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 250 (accept_3_3 20 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 250 (accept_3_3 17 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 250 (accept_3_3 14 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 250 (accept_3_3 11 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 250 (Polychromatic418967fa.accept_19_10_5_3_1_13818 10 81 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 250 (accept_3_3 8 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 250 (accept_3_3 5 81 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 250 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 81 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 250 (accept_3_3 2 81 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 250 (allA_of_3_1 80
  80 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 250 (allA_succ_of_accept 78 79 250
  (Polychromatic418967fa.accept_16_14_15_10_1_5910 78 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 79 250 (accept_3_3 77 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 79 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 250 (accept_3_3 74 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 250
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 250 (accept_3_3 71 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 250 (Polychromatic418967fa.accept_13_5_1_3_1_878 70 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 250 (accept_3_3 68 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 250 (accept_3_3 65 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 250 (accept_3_3 62 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 250 (accept_3_3 59 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 250 (Polychromatic418967fa.accept_13_6_1_3_1_1522 58 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 250 (accept_3_3 56 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 250 (Polychromatic418967fa.accept_18_1_7_16_1_1342 55 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 250
  (Polychromatic418967fa.accept_13_2_1_3_1_419 54 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 250 (accept_3_3 53 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 250 (accept_3_3 50 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 250
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 48 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 79 250 (accept_3_3 47 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 79 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 250 (accept_3_3 44 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 250 (Polychromatic418967fa.accept_13_4_1_3_1_3058
  43 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 250
  (Polychromatic418967fa.accept_23_19_10_20_1_13535 42 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 79 250 (accept_3_3 41 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 79 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 250 (accept_3_3 38 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 250
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 250 (accept_3_3 35 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 250 (Polychromatic418967fa.accept_21_13_16_19_1_1828 34 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 250 (accept_3_3 32 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 250
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 250 (accept_3_3 29 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 250 (accept_3_3 26 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 250 (accept_3_3 23 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 250 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 250 (accept_3_3 20 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 250 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 250 (accept_3_3 17 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 250 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 250 (accept_3_3 14 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 250
  (Polychromatic418967fa.accept_28_12_23_26_1_15082 12 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 79 250 (accept_3_3 11 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 79 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 250 (accept_3_3 8 79 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 250 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7
  79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 250
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 250 (accept_3_3 5 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 250 (accept_3_3 2 79 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 250
  (allA_succ_of_accept 77 78 250 (accept_3_3 77 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  250 2 38 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 250 2 37 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 78 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 250 2 36 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 250 (accept_3_3 71 78 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 250 2 35 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 250 2 34 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 250 2 33 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 250 (accept_3_3 65 78 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 250 2 32 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 250 (Polychromatic418967fa.accept_12_3_6_10_1_576
  63 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 250 2 31 39 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 250
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 61 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 78 250 2 30 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 78 250 (accept_3_3 59 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 250 2 29 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 78 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 250 2 28 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 250 2 27 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 250 (accept_3_3 53 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 250 2 26 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 78 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 250 2 25 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 250 2 24 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 250 (accept_3_3 47 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 250 2 23 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 250 2 22 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 250
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 250 2 21 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 250 (accept_3_3 41 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 250 2 20 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 78 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 250 2 19 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 250 2 18 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 250 (accept_3_3 35 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 250 2 17 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 250 2 16 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 250 2 15 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 250 (accept_3_3 29 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 250 2 14 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 250 2 13 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 250 2 12 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 250 (accept_3_3 23 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 250 2 11 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 250 2 10 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 250 2 9 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 250 (accept_3_3 17 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  250 2 8 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 250 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 250 2 7 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 78 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 250 2 6 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 250 (accept_3_3 11 78 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 250 2 5 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 250
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 78 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 250 2 4 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 250 (Polychromatic418967fa.accept_15_7_3_10_1_817 7 78 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 250 2 3 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 250 (accept_3_3 5 78 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 250 2 2 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 250 2 1 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 250 (allA_of_3_1 77 77
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 250 (allA_succ_of_accept 75 76 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 250 2 37 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 250 2 36 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 250 (accept_3_3 71 76 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 250 2 35 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 69
  76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 250 2 34 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 250 2 33 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 250 (accept_3_3 65 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 250 2 32 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 76 250 (Polychromatic418967fa.accept_22_19_10_8_1_9011 63 76 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 250 2 31 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 76 250 2 30 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 76 250 (accept_3_3 59 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 76 250 2 29 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 76 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 250 2 28 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 250 2 27 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 76 250 (accept_3_3 53 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 250 2 26 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 76 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 250 2 25 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 250 2 24 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 76 250 (accept_3_3 47 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 76 250 2 23 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 76 250 (Polychromatic418967fa.accept_16_13_12_10_1_3540 45 76 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 76 250 2 22 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 76 250 2 21 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 76 250 (accept_3_3 41 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 76 250 2 20 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 76 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 250 2 19 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 250 2 18 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 76 250 (accept_3_3 35 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 76 250 2 17 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 76 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 250 2 16 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 250 2 15 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 250 (accept_3_3 29 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 250 2 14 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 76 250 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 250 2 13 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 250 2 12 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 250 (accept_3_3 23 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 76 250 2 11 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 250 2 10 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 250 2 9 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 250 (accept_3_3 17 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  250 2 8 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 250 2 7 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 76 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 76 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 250 2 6 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 250 (accept_3_3 11 76 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 250 2 5 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 76 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 250 2 4 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 250 2 3 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 250 (accept_3_3 5 76 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 250 2 2 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 250 2 1 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 250 (allA_succ_of_accept
  74 75 250 (accept_3_3 74 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 250 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 250 (accept_3_3 71 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 75 250 5 14 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 250 (accept_3_3 68 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 75 250 5 13 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 250 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 250 (accept_3_3 62 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 250 5 12 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 250 (accept_3_3 59
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 58 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 250 (accept_3_3 56 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 75 250 5 11 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 75 250 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 250 (accept_3_3 53 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 52 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 250 25 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 250 (Polychromatic418967fa.accept_20_8_15_10_1_8045 48 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 250 (accept_3_3 47 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 46
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 250 5 9 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 250 (accept_3_3 44
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 250
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 250 (accept_3_3 41 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 250 5 8 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 250 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 75 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 250 (accept_3_3 38 75 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 250
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 36 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 250 5 7 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 250 (Polychromatic418967fa.accept_19_15_18_3_1_1807 34 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 250 (accept_3_3 32 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 250 5 6 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 250 (accept_3_3 29
  75 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 250 (Polychromatic418967fa.accept_20_7_15_10_1_3628 27 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 250 (accept_3_3 26 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 250 25 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 250 (accept_3_3 23 75 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 75 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 250 5 4 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 250 (accept_3_3 17 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 250
  (Polychromatic418967fa.accept_19_16_18_3_1_15081 16 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 75 250 5 3 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 75 250 (accept_3_3 14 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 250 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 250 (accept_3_3 11 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 250 5 2 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 250 (accept_3_3 8 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 250 5 1 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 250 (Polychromatic418967fa.accept_14_3_5_12_1_4000 3 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 250 (accept_3_3 2 75 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 250 (allA_of_3_1 74 74
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 250 (allA_succ_of_accept 72 73 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 250 (accept_3_3 71 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 250 (accept_3_3 68 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 250 (accept_3_3 65 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 250 (accept_3_3 62 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 250 (Polychromatic418967fa.accept_13_9_8_3_1_3045 61 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 250 (accept_3_3 59 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 250 (accept_3_3 56 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 250
  (Polychromatic418967fa.accept_21_12_10_19_1_12169 54 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 73 250 (accept_3_3 53 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 73 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 250 (accept_3_3 50 73 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 49
  73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 250 (accept_3_3 47 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 250 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 250 (accept_3_3 44 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 250 (accept_3_3 41 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 250 (accept_3_3 38 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 250 (accept_3_3 35 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 250 (Polychromatic418967fa.accept_15_4_13_10_1_1508 34 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 250 (accept_3_3 32 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 250 (accept_3_3 29 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 250 (accept_3_3 26 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 250 (Polychromatic418967fa.accept_17_8_5_12_1_7925 25 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 250 (accept_3_3 23 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 250 (accept_3_3 20 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 250
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 250 (accept_3_3 17 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 250 (accept_3_3 14 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 250 (accept_3_3 11 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 250 (Polychromatic418967fa.accept_17_10_5_12_1_4101 10 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 250 (accept_3_3 8 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 250 (accept_3_3 5 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 250 (accept_3_3 2 73 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 250 (allA_succ_of_accept 71
  72 250 (accept_3_3 71 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 250 2 35 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 250
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 250 2 34 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 72 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 250 2 33 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 250 (accept_3_3 65 72 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 250 2 32 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 250 (Polychromatic418967fa.accept_13_11_7_3_1_894
  63 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 250 2 31 36 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 250
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 250 2 30 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 72 250 (accept_3_3 59 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 250 2 29 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 72 250 (Polychromatic418967fa.accept_21_15_9_19_1_10768 57 72 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 250 2 28 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 250
  (Polychromatic418967fa.accept_19_17_15_3_1_4174 55 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 250 2 27 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 250 (accept_3_3 53 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 250 2 26 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 72 250 (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 72 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 250 2 25 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 250
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 250 2 24 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 250 (accept_3_3 47 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 250 2 23 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 72 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 250 2 22 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 250
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 250 2 21 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 250 (accept_3_3 41 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 250 2 20 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 250 2 19 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 250
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 250 2 18 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 250 (accept_3_3 35 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 250 2 17 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 72 250 (Polychromatic418967fa.accept_20_13_12_10_1_3619 33 72 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 250 2 16 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 250 2 15 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 250 (accept_3_3 29 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 250 2 14 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 250 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 250 2 13 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 250 2 12 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 250 (accept_3_3 23 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 250 2 11 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 72 250 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 250 2 10 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 250
  (Polychromatic418967fa.accept_17_2_4_12_1_6587 19 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 250 2 9 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 250 (accept_3_3 17 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  250 2 8 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 250 (Polychromatic418967fa.accept_20_15_12_10_1_1291 15 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 250 2 7 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 72 250 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 72 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 250 2 6 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 250 (accept_3_3 11 72 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 250 2 5 36 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 250
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 250 2 4 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 250 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 72 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 250 2 3 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 250 (accept_3_3 5 72 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 250 2 2 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 250 2 1 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 250 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1
  72 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 250 (allA_of_3_1 71 71 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 250 (allA_succ_of_accept 69 70 250
  (Polychromatic418967fa.accept_19_12_13_3_1_5447 69 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 250 2 34 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 70 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 250 2 33 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 250 5 13 14 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 70 250 2 32 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 250
  (Polychromatic418967fa.accept_13_11_5_3_1_889 63 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 250 2 31 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 70 250 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 70 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 250 10 6 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 250 (accept_3_3 59 70 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 250 2 29 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 250 (Polychromatic418967fa.accept_17_6_2_12_1_1992 57 70 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 250 2 28 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 70 250 5 11 14 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 70 250 2 27 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 250
  (accept_3_3 53 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 250 2 26 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 250
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 250 10 5 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 250 (Polychromatic418967fa.accept_19_11_13_3_1_9820 49 70 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 250 2 24 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 250 (accept_3_3 47 70 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 250 2 23 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 250 5 9 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 250 2 22 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 250 (Polychromatic418967fa.accept_21_1_7_19_1_9193
  43 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 250 2 21 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 250
  (accept_3_3 41 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 250 10 4 7 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 250
  (Polychromatic418967fa.accept_21_18_7_19_1_12150 39 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 250 2 19 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 250 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 70 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 250 2 18 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 250 5 7 14 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 250 2 17 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 250
  (Polychromatic418967fa.accept_21_12_7_19_1_10736 33 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 250 2 16 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 250 (Polychromatic418967fa.accept_19_12_13_3_1_5447 31 70 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 250 10 3 7 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 250 (accept_3_3 29 70 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 250 2 14 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 250 (Polychromatic418967fa.accept_13_1_5_3_1_888 27
  70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 250 2 13 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 250 5 5 14 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 250 2 12 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 250
  (accept_3_3 23 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 250 2 11 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 250
  (Polychromatic418967fa.accept_13_8_5_3_1_427 21 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 250 10 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 250 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 70 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 250 2 9 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 250 (accept_3_3 17 70 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 250 2 8 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 70 250 5 3 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 250 2 7 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 250 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 70
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 250 2 6 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 250 (accept_3_3 11
  70 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 250 10 1 7 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 250
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 250 2 4 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 250 2 3 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 250 5 1 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 70 250 2 2 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 250 (Polychromatic418967fa.accept_23_3_1_20_1_15080 3 70 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 250 2 1 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 250
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 70 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 250
  (allA_succ_of_accept 68 69 250 (accept_3_3 68 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 250 (accept_3_3 65 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 250 (accept_3_3 62 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 250 (accept_3_3 59 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 250 (accept_3_3 56 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 250 (accept_3_3 53 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 250 (Polychromatic418967fa.accept_27_25_15_7_1_11367 52 69 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 250 (accept_3_3 50 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 250 (accept_3_3 47 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 250
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 45 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 250 (accept_3_3 44 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 250 (accept_3_3 41 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 250 (accept_3_3 38 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 250 (accept_3_3 35 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 250 (Polychromatic418967fa.accept_14_6_13_12_1_810 34 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 250
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 250 (accept_3_3 32 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 250 (accept_3_3 29 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 250 (accept_3_3 26 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 250 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 250 (accept_3_3 23 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 250 (accept_3_3 20 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 250 (accept_3_3 17 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 250 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 250 (accept_3_3 14 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 250 (accept_3_3 11 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 250
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 250 (accept_3_3 8 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 250 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 69 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 250 (accept_3_3 5 69 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 250 (accept_3_3 2 69 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 250 (allA_of_3_1 68 68 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 250 (allA_succ_of_accept 66 67 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 250 (accept_3_3 65 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 250 (accept_3_3 62 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 250 (accept_3_3 59 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 250 (accept_3_3 56 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 250
  (Polychromatic418967fa.accept_21_12_4_19_1_4526 54 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 250 (accept_3_3 53 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 250 (accept_3_3 50 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 250 (accept_3_3 47 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 250 (accept_3_3 44 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 250 (accept_3_3 41 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 250 (accept_3_3 38 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 250 (accept_3_3 35 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 250 (accept_3_3 32 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 250 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 250 (accept_3_3 29 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 250 (accept_3_3 26 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 250 (accept_3_3 23 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 250 (accept_3_3 20 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 250
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 250 (accept_3_3 17 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 250 (accept_3_3 14 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 250 (accept_3_3 11 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 250 (accept_3_3 8 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 250 (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 250 (accept_3_3 5 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  250 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 67 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 250 (accept_3_3 2 67 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 250 (allA_succ_of_accept 65 66
  250 (accept_3_3 65 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 250 2 32 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 250
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 250 2 31 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 250 (Polychromatic418967fa.accept_14_5_10_12_1_1454 61 66 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 250 2 30 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 250 (accept_3_3 59 66 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 250 2 29 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 250 2 28 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 250 2 27 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 250 (accept_3_3 53 66 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 250 2 26 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 51
  66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 250 2 25 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 250 2 24 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 250 (accept_3_3 47 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 250 2 23 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 66 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 250 2 22 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 250 2 21 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 250 (accept_3_3 41 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 250 2 20 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 66 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 250 2 19 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 250 2 18 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 250 (accept_3_3 35 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 250 2 17 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 66 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 250 2 16 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 250 2 15 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 250 (accept_3_3 29 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 250 2 14 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 250 2 13 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 250
  (Polychromatic418967fa.accept_19_6_9_3_1_15079 25 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 250 2 12 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 250 (accept_3_3 23 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 250 2 11 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 66 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 250 2 10 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 250 2 9 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 250 (accept_3_3 17 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  250 2 8 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 250 2 7 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 66 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 250 2 6 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 250 (accept_3_3 11 66 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 250 2 5 33 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 250 2 4 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 250 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 66 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 250 2 3 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 250 (accept_3_3 5 66 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 250 2 2 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 250 2 1 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 250 (allA_of_3_1 65 65 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 250 (allA_succ_of_accept 63 64 250
  (Polychromatic418967fa.accept_19_6_7_3_1_1733 63 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 250 2 31 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 64 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 250 2 30 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 250 (accept_3_3 59 64 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 250 2 29 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 57
  64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 250 2 28 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 250 2 27 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 250 (accept_3_3 53 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 64 250 2 26 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 64 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 250 2 25 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 250 2 24 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 64 250 (accept_3_3 47 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 64 250 2 23 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 64 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 250 2 22 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 250
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 250 2 21 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 64 250 (accept_3_3 41 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 64 250 2 20 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 64 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 250 2 19 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 250 2 18 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 64 250 (accept_3_3 35 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 64 250 2 17 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 64 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 250 2 16 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 250 2 15 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 64 250 (accept_3_3 29 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 64 250 2 14 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 64 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 250 2 13 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 250 2 12 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 64 250 (accept_3_3 23 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 64 250 2 11 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 250 2 10 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 250 2 9 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 250 (accept_3_3 17 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  250 2 8 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 250 2 7 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 64 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 250 2 6 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 250 (accept_3_3 11 64 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 250 2 5 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 250
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 250 2 4 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 64 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 250 2 3 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 250 (accept_3_3 5 64 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 250 2 2 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 250 2 1 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 250 (allA_succ_of_accept 62 63 250
  (accept_3_3 62 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 250 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 250 (accept_3_3 59 63 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 250 (Polychromatic418967fa.accept_14_2_7_12_1_1485 58 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 250 (accept_3_3 56 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 250 (accept_3_3 53 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 250 (Polychromatic418967fa.accept_15_7_3_10_1_817 52 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 250
  (Polychromatic418967fa.accept_14_9_7_12_1_4034 51 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 250 (accept_3_3 50 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 250 (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 250 (accept_3_3 47 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 250 (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 63
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 250 (accept_3_3 44 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 250 (accept_3_3 41 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 250 (Polychromatic418967fa.accept_13_1_11_3_1_901 40 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 250
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 250 (accept_3_3 38 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 250 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 250 (accept_3_3 35 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 250 (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 63
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 250 (accept_3_3 32 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 250 (accept_3_3 29 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 250 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 250
  (Polychromatic418967fa.accept_13_1_11_3_1_901 27 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 250 (accept_3_3 26 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 250 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 250 (accept_3_3 23 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 250 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 63 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 250 (accept_3_3 20 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 250 (accept_3_3 17 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 250 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 250
  (Polychromatic418967fa.accept_13_2_11_3_1_873 15 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 250 (accept_3_3 14 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 250 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 250 (accept_3_3 11 63 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 250 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 63
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 250 (accept_3_3 8 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 250 (accept_3_3 5 63 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 250 (Polychromatic418967fa.accept_19_4_6_3_1_15078 4 63 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 250 (Polychromatic418967fa.accept_23_3_17_20_1_3494
  3 63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 250 (accept_3_3 2 63
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  63 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 250 (allA_of_3_1 62 62 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 250 (allA_succ_of_accept 60 61 250
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 250 (accept_3_3 59 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 250 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 250 (accept_3_3 56 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 250
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 250 (accept_3_3 53 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 250 (accept_3_3 50 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 250 (Polychromatic418967fa.accept_14_7_5_12_1_1439 49 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 250
  (Polychromatic418967fa.accept_29_19_3_18_1_15077 48 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 61 250 (accept_3_3 47 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 61 250 (Polychromatic418967fa.accept_13_7_9_3_1_1504 46 61 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 250 (accept_3_3 44 61 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 250
  (Polychromatic418967fa.accept_17_8_10_12_1_5335 42 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 250 (accept_3_3 41 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 250 (accept_3_3 38 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 250
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 250 (accept_3_3 35 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 250 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 250 (accept_3_3 32 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 250
  (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 61 250 (accept_3_3 29 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 61 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 250 (accept_3_3 26 61 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 250 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  25 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 250
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 250 (accept_3_3 23 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 250 (accept_3_3 20 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 250
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 250 (accept_3_3 17 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 250 (accept_3_3 14 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 250 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 250
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 250 (accept_3_3 11 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 250 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 250 (accept_3_3 8 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 250
  (Polychromatic418967fa.accept_13_6_9_3_1_915 6 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 250 (accept_3_3 5 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  250 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 61 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 250 (accept_3_3 2 61 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 250 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 61 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 250 (allA_succ_of_accept 59 60 250
  (accept_3_3 59 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 250 2 29 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 250 2 28 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 60 250 5 11 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 60 250 2 27 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 60 250 (accept_3_3 53 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 250 2 26 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 60 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 250 10 5 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 49
  60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 250 2 24 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 250 (accept_3_3 47
  60 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 250 2 23 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 250 5 9 12 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 250 2 22 30 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 250 2 21 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 250 (accept_3_3 41 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 250 10 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 250 2 19 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 37
  60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 250 2 18 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 250 5 7 12 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 250 2 17 30 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 250
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 250 2 16 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 60 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 250 10 3 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 250 (accept_3_3 29 60 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 250 2 14 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 250 2 13 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 250 5 5 12 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 250 2 12 30 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 250
  (accept_3_3 23 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 250 2 11 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 250 10 2 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 250 2 9 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 250 (accept_3_3 17 60 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 250 2 8 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 250 5 3 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 250 2 7 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 250 2 6 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 250 (accept_3_3 11
  60 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 250 10 1 6 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 250 2 4 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 250 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 60 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 250 2 3 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 250 5 1 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 250 2 2 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 250 2 1 30 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 250 (allA_of_3_1 59 59 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 250 (allA_succ_of_accept 57 58 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 250 2 28 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 250 2 27 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 250 (accept_3_3 53 58 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 250 2 26 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 51
  58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 250 2 25 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 250
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 250 2 24 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 250 (accept_3_3 47 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 250 2 23 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 250 2 22 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 250
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 250 2 21 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 250 (accept_3_3 41 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 250 2 20 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 250 2 19 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 250 2 18 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 250 (accept_3_3 35 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 250 2 17 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 250 2 16 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 250 2 15 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 250 (accept_3_3 29 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 250 2 14 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 250 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 250 2 13 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 250 2 12 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 250 (accept_3_3 23 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 250 2 11 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 250 2 10 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 250 2 9 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 250 (accept_3_3 17 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  250 2 8 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 250 2 7 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 250 (Polychromatic418967fa.accept_21_13_16_19_1_1828 13 58 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 250 2 6 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 250 (accept_3_3 11 58 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 250 2 5 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 250
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 58 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 250 2 4 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 250 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 58 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 250 2 3 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 250 (accept_3_3 5 58 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 250 2 2 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 250 2 1 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 250 (allA_succ_of_accept 56 57 250
  (accept_3_3 56 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 57 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 250 (accept_3_3 53 57 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 250 (accept_3_3 50 57
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 250 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 250 (accept_3_3 47 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 250 (accept_3_3 44 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 250 (accept_3_3 41 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 250 (accept_3_3 38 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 250
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 250 (accept_3_3 35 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 250 (accept_3_3 32 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 250 (accept_3_3 29 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 250 (accept_3_3 26 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 250 (accept_3_3 23 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 250 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 250 (accept_3_3 20 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 250 (accept_3_3 17 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 250 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 250 (accept_3_3 14 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 250
  (Polychromatic418967fa.accept_21_12_15_19_1_10743 12 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 250 (accept_3_3 11 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 250 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 57 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 250 (accept_3_3 8 57 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 250 (accept_3_3 5 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  250 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 250 (accept_3_3 2 57 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 250)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 250 (allA_of_3_1 56 56 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 250
  (allA_succ_of_accept 54 55 250 (Polychromatic418967fa.accept_19_16_17_3_1_2916 54 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 250 (accept_3_3 53 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 250 5 10 11 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 250 (accept_3_3 47 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 250 5 9 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 250 (accept_3_3 44 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 250 (accept_3_3 41 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  250 5 8 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 250 (accept_3_3 38 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 250 5 7 11 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 250
  (Polychromatic418967fa.accept_14_6_13_12_1_810 34 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 250 (accept_3_3 32 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 250 5 6 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 250 (accept_3_3 29 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 250 (accept_3_3 26 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  250 5 5 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 250 (accept_3_3 23 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 250 5 4 11 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 250
  (Polychromatic418967fa.accept_16_3_7_10_1_3503 19 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 250 (accept_3_3 17 55 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 250 5 3 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 250 (accept_3_3 14 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 250 (accept_3_3 11 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  250 5 2 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 250 (accept_3_3 8 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  250 (Polychromatic418967fa.accept_17_7_4_12_1_4084 7 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 250 5 1 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 250 (accept_3_3 2 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 250))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 250 (allA_succ_of_accept 53 54
  250 (accept_3_3 53 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 250 2 26 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 250
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 250 2 25 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 54 250 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 250 2 24 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 250 (accept_3_3 47 54 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 250 2 23 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  45 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 250 2 22 27 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 250
  (Polychromatic418967fa.accept_19_5_16_3_1_1820 43 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 250 2 21 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 250 (accept_3_3 41 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 250 2 20 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 54 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 250 2 19 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 250
  (Polychromatic418967fa.accept_13_11_2_3_1_883 37 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 250 2 18 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 250 (accept_3_3 35 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 250 2 17 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 250 2 16 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 250 2 15 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 250 (accept_3_3 29 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 250 2 14 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 250 2 13 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 250
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 250 2 12 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 250 (accept_3_3 23 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 250 2 11 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 250 2 10 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 250
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 250 2 9 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 250 (accept_3_3 17 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  250 2 8 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 250 2 7 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 250 (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 54 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 250 2 6 27 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 250 (accept_3_3 11 54 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 250 2 5 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 250 2 4 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 250 (Polychromatic418967fa.accept_17_7_3_12_1_4098 7 54 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 250 2 3 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 250 (accept_3_3 5 54 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 250 2 2 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 250 2 1 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 250 (Polychromatic418967fa.accept_13_1_2_3_1_911 1
  54 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  250)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 250 (allA_of_3_1 53 53 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 250 (allA_succ_of_accept 51 52 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 250 2 25 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 250 2 24 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 52 250 (accept_3_3 47 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 52 250 2 23 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 52 250 (Polychromatic418967fa.accept_19_7_14_3_1_1793 45 52 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 250 2 22 26 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 250 2 21 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 52 250 (accept_3_3 41 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 52 250 2 20 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 52 250 (Polychromatic418967fa.accept_36_3_16_34_1_15076 39 52 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 250 2 19 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 250 2 18 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 52 250 (accept_3_3 35 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 52 250 2 17 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 250 (Polychromatic418967fa.accept_14_5_10_12_1_1454 33 52 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 250 2 16 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 250 2 15 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 250 (accept_3_3 29 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 250 2 14 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 52 250 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 52 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 250 2 13 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 250 2 12 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 52 250 (accept_3_3 23 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 52 250 2 11 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 250 (Polychromatic418967fa.accept_27_21_25_7_1_13258 21 52 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 250 2 10 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 250 2 9 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 250 (accept_3_3 17 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  250 2 8 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 250 2 7 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 52 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 52 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 250 2 6 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 250 (accept_3_3 11 52 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 250 2 5 26 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 250 2 4 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 250 2 3 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 250 (accept_3_3 5 52 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 250 2 2 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 250 (Polychromatic418967fa.accept_15_3_7_10_1_2324 3 52 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 250 2 1 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  250)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 250 (allA_succ_of_accept 50 51 250 (accept_3_3
  50 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 250 (accept_3_3 47 51 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 250 (accept_3_3 44 51
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 250 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 250 (accept_3_3 41 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 250 (accept_3_3 38 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 250
  (Polychromatic418967fa.accept_21_15_9_19_1_10768 36 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 250 (accept_3_3 35 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 250 (Polychromatic418967fa.accept_15_4_6_10_1_823 34 51 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 250 (accept_3_3 32 51 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 250 (accept_3_3 29 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 250 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 250 (accept_3_3 26 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 250 (accept_3_3 23 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 250 (accept_3_3 20 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 250 (accept_3_3 17 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 250 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 250 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 250 (accept_3_3 14 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 250 (accept_3_3 11 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 250 (accept_3_3 8 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 250 (accept_3_3 5 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 250 (accept_3_3 2 51 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 250)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 250 (allA_of_3_1 50 50 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 250
  (allA_succ_of_accept 48 49 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 250 (accept_3_3 47 49 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 250 (accept_3_3 44 49
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 250 (accept_3_3 41 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 250 (accept_3_3 38 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 250
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 250 (accept_3_3 35 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 250 (Polychromatic418967fa.accept_21_13_7_19_1_4505 34 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 250 (accept_3_3 32 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 250 (accept_3_3 29 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 250 (accept_3_3 26 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 250 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 250 (accept_3_3 23 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 250 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 250 (accept_3_3 20 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 250
  (Polychromatic418967fa.accept_17_1_15_12_1_7907 18 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 250 (accept_3_3 17 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 250 (accept_3_3 14 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 250 (accept_3_3 11 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 250 (accept_3_3 8 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 250 (accept_3_3 5 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  250 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 250 (accept_3_3 2 49 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 250)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 250 (allA_succ_of_accept 47 48 250 (accept_3_3 47 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 250 2 23 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 48 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 250 2 22 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 250 2 21 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 48 250 (accept_3_3 41 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 250 2 20 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 250 2 19 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 250 2 18 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 48 250 (accept_3_3 35 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 250 2 17 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 48 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 250 2 16 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 250
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 250 2 15 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 250 (accept_3_3 29 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 250 2 14 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 250 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 48 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 250 2 13 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 250 2 12 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 250 (accept_3_3 23 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 250 2 11 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 48 250 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 250 2 10 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 250 2 9 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 250 (accept_3_3 17 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  250 2 8 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 250 2 7 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 48 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 250 2 6 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 250 (accept_3_3 11 48 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 250 2 5 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 250
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 48 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 250 2 4 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 48 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 250 2 3 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 250 (accept_3_3 5 48 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 250 2 2 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 250 (Polychromatic418967fa.accept_21_3_6_19_1_3125 3 48 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 250 2 1 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  250)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 250 (allA_of_3_1 47 47 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 250 (allA_succ_of_accept 45 46 250 (Polychromatic418967fa.accept_16_13_14_10_1_1669
  45 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 250 2 22 23 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 250 2 21 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 46 250 (accept_3_3 41 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 46 250 2 20 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 46 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 250 2 19 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 250 2 18 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 250 (accept_3_3 35 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 250 2 17 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 250 2 16 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 250 2 15 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 250 (accept_3_3 29 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 250 2 14 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 250 2 13 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 250
  (Polychromatic418967fa.accept_19_6_8_3_1_11219 25 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 250 2 12 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 250 (accept_3_3 23 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 250 2 11 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 250 2 10 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 250
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 250 2 9 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 250 (accept_3_3 17 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  250 2 8 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 250 2 7 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 46 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 250 2 6 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 250 (accept_3_3 11 46 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 250 2 5 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 250
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 250 2 4 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 46 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 250 2 3 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 250 (accept_3_3 5 46 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 250 2 2 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 250 2 1 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  250)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 250 (allA_succ_of_accept 44 45 250 (accept_3_3 44 45
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 250 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 250 (accept_3_3 41 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45
  250 5 8 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  45 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 250 (accept_3_3 38 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 250 5 7 9 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 250
  (Polychromatic418967fa.accept_19_15_7_3_1_4143 34 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 250 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 250 (accept_3_3 32 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 250 5 6 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 250 (accept_3_3 29 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 250 (Polychromatic418967fa.accept_16_12_13_10_1_2637 28 45 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 250 (accept_3_3 26 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45
  250 5 5 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  45 250 (Polychromatic418967fa.accept_19_5_7_3_1_6990 24 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 250 (accept_3_3 23 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 250 (Polychromatic418967fa.accept_16_5_13_10_1_3664 21 45
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 250 5 4 9 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 250 (accept_3_3 17 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 250 5 3 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 250 (accept_3_3 14 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 250
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 250 (accept_3_3 11 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 250 5 2 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 45 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 250 (accept_3_3 8 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 45 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 6
  45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 250 5 1 9 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 250
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 45 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 250 (accept_3_3 2 45 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 250))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  250 (allA_of_3_1 44 44 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 250 (allA_succ_of_accept 42 43 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 42 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 250 (accept_3_3 41 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 250 (accept_3_3 38 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 250
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 250 (accept_3_3 35 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 250 (accept_3_3 32 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 250
  (Polychromatic418967fa.accept_26_4_17_16_1_15075 30 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 43 250 (accept_3_3 29 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 43 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 43 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 250 (accept_3_3 26 43 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 250 (accept_3_3 23 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 250 (Polychromatic418967fa.accept_17_5_9_12_1_9156 22 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 250 (accept_3_3 20 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 250 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 43 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 250 (accept_3_3 17 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 250 (accept_3_3 14 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 250
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 250 (accept_3_3 11 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 250 (accept_3_3 8 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 250 (accept_3_3 5 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  250 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 250 (accept_3_3 2 43 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 250))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 250
  (allA_succ_of_accept 41 42 250 (accept_3_3 41 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  250 2 20 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 42 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 250 2 19 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 250 2 18 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 250 (accept_3_3 35 42 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 250 2 17 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 250
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 250 2 16 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 250 2 15 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 250 (accept_3_3 29 42 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 250 2 14 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 250 (Polychromatic418967fa.accept_12_3_6_10_1_576
  27 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 250 2 13 21 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 250
  (Polychromatic418967fa.accept_19_6_4_3_1_11188 25 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 250 2 12 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 250 (accept_3_3 23 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 250 2 11 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 42 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 250 2 10 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 250 2 9 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 250 (accept_3_3 17 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  250 2 8 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 250 2 7 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 42 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 250 2 6 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 250 (accept_3_3 11 42 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 250 2 5 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 250
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 250 2 4 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 250 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 42 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 250 2 3 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 250 (accept_3_3 5 42 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 250 2 2 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 250 2 1 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  250)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 250 (allA_of_3_1 41 41 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 250 (allA_succ_of_accept 39 40 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 250 2 19 20 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 250 2 18 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 40 250 5 7 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 40 250 2 17 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 40 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 250 2 16 20 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 250 10 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 250 (accept_3_3 29 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  250 2 14 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 40 250 (Polychromatic418967fa.accept_17_10_6_12_1_11635 27 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 250 2 13 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 250 5 5 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 250 2 12 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 250 (accept_3_3 23 40 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 40 250 2 11 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 40 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 250 10 2 4 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 250 2 9 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 250 (accept_3_3 17 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  250 2 8 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40
  250 5 3 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40
  250 2 7 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  40 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 40 250 2 6 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 40 250 (accept_3_3 11 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 40 250 10 1 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 40 250 (Polychromatic418967fa.accept_22_9_18_8_1_8979 9 40 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 250 2 4 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 250 2 3 20 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 250 5 1 8 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 250 2 2 20 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 250 2 1 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 40 250)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 250
  (allA_succ_of_accept 38 39 250 (accept_3_3 38 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 250 (accept_3_3 35 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 250 (accept_3_3 32 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 250 (accept_3_3 29 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 250 (accept_3_3 26 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 250 (accept_3_3 23 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 250 (accept_3_3 20 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 250 (accept_3_3 17 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 250 (accept_3_3 14 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 250 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 250 (accept_3_3 11 39 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 250 (accept_3_3 8 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 250 (accept_3_3 5 39 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 250 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3
  39 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 250 (accept_3_3 2 39 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  250))))))))))))))))))))))))))))))))))))))) (allB_succ 38 250 (allA_of_3_1 38 38 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 250 (allA_succ_of_accept 36 37 250 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 37 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 250 (accept_3_3 35 37 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  34 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 250 (accept_3_3 32 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 250 (accept_3_3 29 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 250 (accept_3_3 26 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 250 (accept_3_3 23 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 250 (accept_3_3 20 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 250 (accept_3_3 17 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 250 (accept_3_3 14 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 250 (accept_3_3 11 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 250 (accept_3_3 8 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 250 (accept_3_3 5 37 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 250 (accept_3_3 2 37 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 250 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1
  37 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  250))))))))))))))))))))))))))))))))))))) (allB_succ 36 250 (allA_succ_of_accept 35 36 250 (accept_3_3 35 36 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 250 2 17 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 250
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 250 2 16 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 36 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 250 2 15 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 250 (accept_3_3 29 36 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 250 2 14 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 250 2 13 18 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 250 2 12 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 36 250 (accept_3_3 23 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 250 2 11 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 36 250 (Polychromatic418967fa.accept_17_4_2_12_1_6554 21 36 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 250 2 10 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 250
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 250 2 9 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 250 (accept_3_3 17 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  250 2 8 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 250 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 250 2 7 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 36 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 250 2 6 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 250 (accept_3_3 11 36 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 250 2 5 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 250
  (Polychromatic418967fa.accept_20_9_16_10_1_3559 9 36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 250 2 4 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 250 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 36 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 250 2 3 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 250 (accept_3_3 5 36 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 250 2 2 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 250 2 1 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 250 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  36 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  250)))))))))))))))))))))))))))))))))))) (allB_succ 35 250 (allA_of_3_1 35 35 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 34 250 (allA_succ_of_accept 33 34 250 (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 34 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 250 2 16 17 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 250
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 250 2 15 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 34 250 (accept_3_3 29 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 34 250 2 14 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 250 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 34 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 250 2 13 17 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 250 2 12 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 250 (accept_3_3 23 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 250 2 11 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 250 (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 34 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 250 2 10 17 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 250
  (Polychromatic418967fa.accept_26_19_8_16_1_15074 19 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 34 250 2 9 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 34 250 (accept_3_3 17 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 34 250 2 8 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 34 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 250 2 7 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 250 (Polychromatic418967fa.accept_14_13_6_12_1_3126
  13 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 250 2 6 17 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 250 (accept_3_3 11
  34 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 250 2 5 17 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 250
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 34 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 250 2 4 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 250 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 34 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 250 2 3 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 250 (accept_3_3 5 34 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 250 2 2 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 250 (Polychromatic418967fa.accept_28_3_6_26_1_15073 3 34 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 250 2 1 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 250))))))))))))))))))))))))))))))))))
  (allB_succ 33 250 (allA_succ_of_accept 32 33 250 (accept_3_3 32 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 250 (accept_3_3 29 33 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 250 (accept_3_3 26 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 250 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 250 (accept_3_3 23 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 33 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 250 (accept_3_3 20 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 250 (accept_3_3 17 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 250 (Polychromatic418967fa.accept_19_16_14_3_1_11194 16 33 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 250 (accept_3_3 14 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 250 (accept_3_3 11 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 250
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 250 (accept_3_3 8 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 250 (accept_3_3 5 33 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 250 (accept_3_3 2 33 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 250)))))))))))))))))))))))))))))))))
  (allB_succ 32 250 (allA_of_3_1 32 32 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 250
  (allA_succ_of_accept 30 31 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 250 (accept_3_3 29 31 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 250 (accept_3_3 26 31
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 250 (Polychromatic418967fa.accept_4_1_3_2_1_3
  25 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 250 (accept_3_3 23 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 250 (accept_3_3 20 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 250
  (Polychromatic418967fa.accept_22_18_9_8_1_1365 18 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 250 (accept_3_3 17 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 250 (accept_3_3 14 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 250 (accept_3_3 11 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 250 (accept_3_3 8 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 250 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 31 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 250 (accept_3_3 5 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  250 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 250 (accept_3_3 2 31 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 250))))))))))))))))))))))))))))))) (allB_succ 30 250
  (allA_succ_of_accept 29 30 250 (accept_3_3 29 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  250 2 14 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 30 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 250 2 13 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 250 5 5 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 250 2 12 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 250 (accept_3_3 23 30 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 250 2 11 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 250 10 2 3 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 250 2 9 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 250 (accept_3_3 17 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30
  250 2 8 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30
  250 5 3 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30
  250 2 7 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  30 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 30 250 2 6 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 250 (accept_3_3 11 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 250 10 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 250 2 4 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 250 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 30 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 250 2 3 15 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 250 5 1 6 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 250 2 2 15 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 250 2 1 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 250)))))))))))))))))))))))))))))) (allB_succ 29 250 (allA_of_3_1 29 29
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 250 (allA_succ_of_accept 27 28 250
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 250 2 13 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 28 250 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 28 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 250 2 12 14 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 250 (accept_3_3 23 28 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 250 2 11 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 250 2 10 14 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 250 2 9 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 250 (accept_3_3 17 28 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  250 2 8 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 250 2 7 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 28 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 250 2 6 14 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 250 (accept_3_3 11 28 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 250 2 5 14 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 250
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 250 2 4 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 250 2 3 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 250 (accept_3_3 5 28 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 250 2 2 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 250 2 1 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  28 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 250))))))))))))))))))))))))))))
  (allB_succ 27 250 (allA_succ_of_accept 26 27 250 (accept_3_3 26 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 27 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 250 (accept_3_3 23 27 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 22
  27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 250 (accept_3_3 20 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 250 (accept_3_3 17 27 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 250 (Polychromatic418967fa.accept_23_16_4_20_1_15072 16 27 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 250 (accept_3_3 14 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 250 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 27 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 250 (accept_3_3 11 27 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 250 (Polychromatic418967fa.accept_22_10_5_8_1_8954 10 27
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 250 (accept_3_3 8 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 250 (accept_3_3 5 27 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 250 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  27 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 250 (accept_3_3 2 27 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 250)))))))))))))))))))))))))))
  (allB_succ 26 250 (allA_of_3_1 26 26 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 250
  (allA_succ_of_accept 24 25 250 (Polychromatic418967fa.accept_19_5_6_3_1_5578 24 25 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 250 (accept_3_3 23 25 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 250 5 4 5 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 250 (Polychromatic418967fa.accept_19_18_6_3_1_8405 18 25 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 250 (accept_3_3 17 25 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 250 5 3 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 250 (accept_3_3 14 25 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 250
  (Polychromatic418967fa.accept_20_12_5_10_1_9540 12 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 250 (accept_3_3 11 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  250 5 2 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 250 (accept_3_3 8 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 250 5 1 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 250 (accept_3_3 2 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 250))))))))))))))))))))))))) (allB_succ 24 250 (allA_succ_of_accept 23 24 250 (accept_3_3 23 24 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 250 2 11 12 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 250 2 10 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 250 2 9 12 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 250 (accept_3_3 17 24 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 250 2 8 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  24 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 250 2 7 12 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 250 2 6 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 250 (accept_3_3 11 24 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  250 2 5 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 250 2 4 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 250 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 24 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 250 2 3 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 250 (accept_3_3 5 24 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 250 2 2 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 250 2 1 12 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 250)))))))))))))))))))))))) (allB_succ 23 250 (allA_of_3_1 23 23 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 250 (allA_succ_of_accept 21 22 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 250 2 10 11 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 250 2 9 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 250 (accept_3_3 17 22 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  250 2 8 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 250 2 7 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 22 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 250 2 6 11 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 250 (accept_3_3 11 22 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 250 2 5 11 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 250
  (Polychromatic418967fa.accept_17_9_5_12_1_6606 9 22 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 250 2 4 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 250 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 22 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 250 2 3 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 250 (accept_3_3 5 22 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 250 2 2 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 250 2 1 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 250)))))))))))))))))))))) (allB_succ 21
  250 (allA_succ_of_accept 20 21 250 (accept_3_3 20 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 250 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 250 (accept_3_3 17 21 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 250 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 21 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 250 (accept_3_3 14 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 250 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 21 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 250 (accept_3_3 11 21 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 250
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 250 (accept_3_3 8 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 250 (accept_3_3 5 21 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 250 (accept_3_3 2 21 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 250))))))))))))))))))))) (allB_succ 20
  250 (allA_of_3_1 20 20 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 250 (allA_succ_of_accept 18 19 250
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 250 (accept_3_3 17 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 250 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 250 (accept_3_3 14 19 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 250 (accept_3_3 11 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 250 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 250 (accept_3_3 8 19 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 250 (Polychromatic418967fa.accept_14_7_5_12_1_1439 7 19 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 250 (accept_3_3 5 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 250 (accept_3_3 2 19 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 250))))))))))))))))))) (allB_succ 18 250 (allA_succ_of_accept 17
  18 250 (accept_3_3 17 18 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 250 2 8 9 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 250 2 7 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 250 2 6 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 250 (accept_3_3 11 18 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 250 2 5 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 250 2 4 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 250 (Polychromatic418967fa.accept_15_7_3_10_1_817 7
  18 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 250 2 3 9 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 250 (accept_3_3 5 18
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 250 2 2 9 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 250
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 18 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 250 2 1 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 250 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 250)))))))))))))))))) (allB_succ 17 250 (allA_of_3_1 17 17 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 250 (allA_succ_of_accept 15 16 250
  (Polychromatic418967fa.accept_19_15_16_3_1_8409 15 16 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 250 2 7 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 250 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 16 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 250 2 6 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 250 (accept_3_3 11 16 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 250 2 5 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 250 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 16 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 250 2 4 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 250 2 3 8 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 250 (accept_3_3 5 16
  250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 250 2 2 8 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 250 2 1 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 16 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 250)))))))))))))))) (allB_succ 15 250 (allA_succ_of_accept 14 15 250
  (accept_3_3 14 15 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 250 (accept_3_3 11 15 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 250 5 2 3 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 250 (accept_3_3 8 15 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 250
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 250 5 1 3 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 250 (accept_3_3 2 15 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 250))))))))))))))) (allB_succ 14 250
  (allA_of_3_1 14 14 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 250 (allA_succ_of_accept 12 13 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 250 (accept_3_3 11 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 250 (accept_3_3 8 13 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 250
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 250 (accept_3_3 5 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 250 (accept_3_3 2 13 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 250))))))))))))) (allB_succ 12 250 (allA_succ_of_accept 11 12
  250 (accept_3_3 11 12 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 250 2 5 6 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 250
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 12 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 250 2 4 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 250 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 12 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 250 2 3 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 250 (accept_3_3 5 12 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 250 2 2 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 250 (Polychromatic418967fa.accept_16_3_12_10_1_315 3 12 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 250 2 1 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 250)))))))))))) (allB_succ 11 250
  (allA_of_3_1 11 11 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 250 (allA_succ_of_accept 9 10 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 250 2 4 5 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 250 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 10 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 250 2 3 5 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 250 5 1 2 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 250 2 2 5 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 250 2 1 5 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 250)))))))))) (allB_succ 9 250 (allA_succ_of_accept 8 9 250 (accept_3_3 8 9 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 250
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 250 (accept_3_3 5 9 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 250 (accept_3_3 2 9 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 250))))))))) (allB_succ 8 250 (allA_of_3_1 8 8 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 250 (allA_succ_of_accept 6 7 250
  (Polychromatic418967fa.accept_19_6_7_3_1_1733 6 7 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 250 (accept_3_3 5 7 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 250
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 7 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 250 (accept_3_3 2 7 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 250))))))) (allB_succ 6 250 (allA_succ_of_accept 5 6 250
  (accept_3_3 5 6 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 250 2 2 3 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 250 2 1 3 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 250)))))) (allB_succ 5 250 (allA_of_3_1 5 5 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 250 (allA_succ_of_accept 3 4 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 250 2 1 2 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 250)))) (allB_succ 3 250 (allA_succ_of_accept 2 3 250 (accept_3_3 2 3 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 250))) (allB_succ 2 250 (allA_of_3_1 2 2 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  250))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


