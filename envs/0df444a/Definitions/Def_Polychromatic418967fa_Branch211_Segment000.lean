-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch211_Segment000
-- name    : Polychromatic418967fa_Branch211_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:32:43.695472+00:00
-- url     : https://prove2.me/theorems/46a4e0f4-63da-4d8f-a2fa-23122b1fe455
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

def Polychromatic418967fa.branch_211_segment_000 : allB 126 211 :=
  allB_succ' 87 125 211 (Eq.refl Bool.true) (allA_of_3_1 87 125 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  88 124 211 (Eq.refl Bool.true) (allA_succ_of_accept 87 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 124 211 (accept_3_3 86 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 124 211 (Polychromatic418967fa.accept_10_5_4_1_1_842
  85 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 124 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 124 211 (accept_3_3 83 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 124 211 (accept_3_3 80 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 124 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 124 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 124 211 (accept_3_3 77 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 124 211 (accept_3_3 74 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 124 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 124 211
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 124 211 (accept_3_3 71 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 124 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 124 211 (accept_3_3 68 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 124 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 124 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 124 211 (accept_3_3 65 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 124 211 (accept_3_3 62 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 124 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 124 211 (accept_3_3 59 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 124 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 211 (accept_3_3 56 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 211
  (Polychromatic418967fa.accept_21_12_19_1_1_2028 54 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 124 211 (accept_3_3 53 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 124 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 124 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 211 (accept_3_3 50 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 211
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 124 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 211 (accept_3_3 47 124 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 124 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 45
  124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 211 (accept_3_3 44
  124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 211
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 124 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 211 (accept_3_3 41 124 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 124 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 211 (accept_3_3 38 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 211 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 211 (accept_3_3 35 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 211 (accept_3_3 32 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 211 (accept_3_3 29 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 211 (accept_3_3 26 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 211 (accept_3_3 23 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 211 (accept_3_3 20 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 211 (accept_3_3 17 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 211 (Polychromatic418967fa.accept_21_16_19_1_1_6320 16 124 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 211 (accept_3_3 14 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 211 (accept_3_3 11 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 211 (accept_3_3 8 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 211 (accept_3_3 5 124 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 124 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 211 (accept_3_3 2 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 124 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 89 123 211 (Eq.refl Bool.true) (allA_succ_of_accept 88 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57
  88 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 123 211 (accept_3_3 86 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 123 211 (Polychromatic418967fa.accept_28_1_11_15_1_12513 85 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 211 (accept_3_3 83 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 123 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 123 211 (accept_3_3 80 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 123 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 123 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 211 (accept_3_3 77 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 123 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 123 211 (accept_3_3 74 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 123 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 123 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 211 (accept_3_3 71 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 123 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 123 211 (accept_3_3 68 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 123 211 (Polychromatic418967fa.accept_21_4_18_1_1_6333 67 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 123 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 211 (accept_3_3 65 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 211
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 211 (accept_3_3 62 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 123 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 211 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 123
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 211 (accept_3_3 59 123
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 211
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 123 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 123 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 211 (accept_3_3 56 123 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 123 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 211 (Polychromatic418967fa.accept_7_5_4_1_1_412
  54 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 211 (accept_3_3 53
  123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 211
  (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 123 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 123 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 211 (accept_3_3 50 123 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 123 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 211 (accept_3_3 47 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 211 (accept_3_3 44 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 211
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 211 (accept_3_3 41 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 211 (accept_3_3 38 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 211
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 211 (accept_3_3 35 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 211 (accept_3_3 32 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 211 (accept_3_3 29 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 211 (accept_3_3 26 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 123 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 211 (accept_3_3 23 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 211 (accept_3_3 20 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 211
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 211 (accept_3_3 17 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 211 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 211 (accept_3_3 14 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 211 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 123
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 211 (accept_3_3 11 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 211 (accept_3_3 8 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 211 (accept_3_3 5 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 211 (accept_3_3 2 123 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 123 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 122 211
  (Eq.refl Bool.true) (allA_of_3_1 90 122 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 121 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 90 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 211 (accept_3_3 89 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 211 (Polychromatic418967fa.accept_20_8_1_11_1_5125 88 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 211 (accept_3_3 86 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 85 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 211 (Polychromatic418967fa.accept_20_4_1_11_1_9646 84 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 211 (accept_3_3 83 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 211
  (Polychromatic418967fa.accept_17_13_2_7_1_6122 81 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 211 (accept_3_3 80 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 79 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 211 (accept_3_3 77 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 211
  (Polychromatic418967fa.accept_22_9_11_13_1_10890 75 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 121 211 (accept_3_3 74 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 121 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 121 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 211 (accept_3_3 71 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 121 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 121 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 211 (accept_3_3 68 121 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 121 211 (Polychromatic418967fa.accept_20_7_1_11_1_3766 67 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 211 (accept_3_3 65 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 64 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 211 (Polychromatic418967fa.accept_17_12_2_7_1_3813 63 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 211 (accept_3_3 62 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 211 (Polychromatic418967fa.accept_19_4_7_2_1_6944 61 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 211
  (Polychromatic418967fa.accept_16_12_9_3_1_5363 60 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 211 (accept_3_3 59 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 211 (Polychromatic418967fa.accept_20_17_1_11_1_6555 57 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 211 (accept_3_3 56 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 211 (accept_3_3 53 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 211 (accept_3_3 50 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 211 (Polychromatic418967fa.accept_17_15_2_7_1_7389 49 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 211 (accept_3_3 47 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 211 (accept_3_3 44 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 211 (Polychromatic418967fa.accept_17_9_2_7_1_2689 43 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 211 (accept_3_3 41 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 40 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 211 (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 211 (accept_3_3 38 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 211 (Polychromatic418967fa.accept_20_17_1_11_1_6555 37 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 211
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 211 (accept_3_3 35 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 211 (accept_3_3 32 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 211 (accept_3_3 29 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 211 (Polychromatic418967fa.accept_16_12_9_3_1_5363 28 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 211 (accept_3_3 26 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 211 (accept_3_3 23 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 211 (Polychromatic418967fa.accept_23_21_6_4_1_7326 21 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 211 (accept_3_3 20 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 211 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 121
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 211 (accept_3_3 17 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 211 (Polychromatic418967fa.accept_19_16_7_2_1_12512 16 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 211 (Polychromatic418967fa.accept_17_15_2_7_1_7389 15 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 211 (accept_3_3 14 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 211
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 211 (accept_3_3 11 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 211 (Polychromatic418967fa.accept_17_9_2_7_1_2689 9 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 211 (accept_3_3 8 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 211 (accept_3_3 5 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 211 (Polychromatic418967fa.accept_19_4_7_2_1_6944 4 121 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 211 (accept_3_3 2 121 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 121 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 120 211
  (Eq.refl Bool.true) (allA_succ_of_accept 91 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 120 211
  (Polychromatic418967fa.accept_21_6_15_1_1_2050 90 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 120 211 (accept_3_3 89 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 211 (accept_3_3 86 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 211 (Polychromatic418967fa.accept_16_5_8_3_1_4240 85 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 120 211
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 84 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 120 211 (accept_3_3 83 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 120 211 (Polychromatic418967fa.accept_21_18_15_1_1_9470 81 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 211 (accept_3_3 80 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 120 211 (accept_3_3 77 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 120 211 (Polychromatic418967fa.accept_16_12_8_3_1_4241 76 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 120 211 (Polychromatic418967fa.accept_16_11_8_3_1_3183 75 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 211 (accept_3_3 74 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 211
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 120 211 (accept_3_3 71 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 211 (accept_3_3 68 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 211
  (Polychromatic418967fa.accept_21_3_15_1_1_2046 66 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 120 211 (accept_3_3 65 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 120 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621 63 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 211 (accept_3_3 62 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 120 211 (accept_3_3 59 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 120 211 (Polychromatic418967fa.accept_14_2_8_1_1_1647 58 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 120 211 (Polychromatic418967fa.accept_18_3_12_13_1_3307 57 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 211 (accept_3_3 56 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 211
  (Polychromatic418967fa.accept_21_12_15_1_1_12511 54 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 211 (accept_3_3 53 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 211 (accept_3_3 50 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621
  49 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 211
  (Polychromatic418967fa.accept_19_10_6_2_1_6907 48 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 211 (accept_3_3 47 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 211 (accept_3_3 44 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 211 (accept_3_3 41 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 211 (Polychromatic418967fa.accept_21_19_15_1_1_6345 40 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 120 211 (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 211 (accept_3_3 38 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 211
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 211 (accept_3_3 35 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 211 (accept_3_3 32 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 211 (Polychromatic418967fa.accept_19_12_6_2_1_5424 31 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 211
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 120 211 (accept_3_3 29 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 211 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 211 (accept_3_3 26 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 211 (accept_3_3 23 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 211 (Polychromatic418967fa.accept_19_3_6_2_1_6910 22 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 211 (accept_3_3 20 120 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 211
  (Polychromatic418967fa.accept_21_18_15_1_1_9470 18 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 211 (accept_3_3 17 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 211 (accept_3_3 14 120 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 211
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 120 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 211 (accept_3_3 11 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 211 (Polychromatic418967fa.accept_14_9_8_1_1_2381
  9 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 211 (accept_3_3 8
  120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 120 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 211 (accept_3_3 5 120 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 120 211 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 120 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 211
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 211 (accept_3_3 2 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 119 211
  (Eq.refl Bool.true) (allA_of_3_1 93 119 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 118 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 211 (accept_3_3 92 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 211 (Polychromatic418967fa.accept_14_7_6_1_1_1656 91 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 211
  (Polychromatic418967fa.accept_19_14_4_2_1_2840 90 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 211 (accept_3_3 89 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 211 (accept_3_3 86 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 211 (accept_3_3 83 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 211 (accept_3_3 80 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 211 (accept_3_3 77 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 211 (accept_3_3 74 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 211 (accept_3_3 71 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 211 (accept_3_3 68 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 67 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 211 (accept_3_3 65 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 211 (accept_3_3 62 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 211 (accept_3_3 59 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 211 (accept_3_3 56 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 118 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 211 (accept_3_3 53 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 211 (accept_3_3 50 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 211 (accept_3_3 47 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 46 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 211 (accept_3_3 44 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 211 (accept_3_3 41 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 211 (accept_3_3 38 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 211
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 211 (accept_3_3 35 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 211 (accept_3_3 32 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 211 (accept_3_3 29 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 211 (accept_3_3 26 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 211 (accept_3_3 23 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 211 (Polychromatic418967fa.accept_18_4_10_13_1_5883 22 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 211 (accept_3_3 20 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 211
  (Polychromatic418967fa.accept_13_5_1_3_1_878 18 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 211 (accept_3_3 17 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 211 (accept_3_3 14 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 211 (accept_3_3 11 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 211 (accept_3_3 8 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 211 (accept_3_3 5 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 118 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 211 (accept_3_3 2 118 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 117
  211 (Eq.refl Bool.true) (allA_succ_of_accept 94 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 93 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 211 (accept_3_3 92 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 211 (Polychromatic418967fa.accept_21_7_12_1_1_952 91 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 211 (accept_3_3 89 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 211 (accept_3_3 86 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 211 (Polychromatic418967fa.accept_20_5_17_11_1_6571 85 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 211 (accept_3_3 83 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 211 (accept_3_3 80 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 211 (accept_3_3 77 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 211
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 211 (accept_3_3 74 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 211 (Polychromatic418967fa.accept_16_8_5_3_1_4297 72 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 211 (accept_3_3 71 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 211 (accept_3_3 68 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 211 (accept_3_3 65 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 211 (accept_3_3 62 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 211 (Polychromatic418967fa.accept_20_1_17_11_1_8119 61 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 211 (accept_3_3 59 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 57 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 211 (accept_3_3 56 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 211 (accept_3_3 53 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 211 (accept_3_3 50 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 211 (accept_3_3 47 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 211 (accept_3_3 44 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 211 (accept_3_3 41 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 211 (accept_3_3 38 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 211 (Polychromatic418967fa.accept_19_18_3_2_1_6939 37 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 211 (accept_3_3 35 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 211
  (Polychromatic418967fa.accept_25_8_17_11_1_12510 33 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 211 (accept_3_3 32 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 117 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 211 (accept_3_3 29 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 211 (accept_3_3 26 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 211 (accept_3_3 23 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 211 (accept_3_3 20 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 211 (accept_3_3 17 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 211 (accept_3_3 14 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 211 (Polychromatic418967fa.accept_19_12_3_2_1_12509 12 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 211 (accept_3_3 11 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 211
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 211 (accept_3_3 8 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 211 (Polychromatic418967fa.accept_21_7_12_1_1_952 7 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 211 (accept_3_3 5 117 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 211 (accept_3_3 2 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 211 (Polychromatic418967fa.accept_19_1_3_2_1_11168 1 117 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 116
  211 (Eq.refl Bool.true) (allA_of_3_1 96 116 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 115 211
  (Eq.refl Bool.true) (allA_succ_of_accept 96 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 211 (accept_3_3 95 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 94 115
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 211 (accept_3_3 92 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 211 (Polychromatic418967fa.accept_19_14_1_2_1_11172 90 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 211 (accept_3_3 89 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 115 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 211 (accept_3_3 86 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 211 (accept_3_3 83 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 211 (accept_3_3 80 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 211 (accept_3_3 77 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 76 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 211 (accept_3_3 74 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 211 (accept_3_3 71 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 211 (Polychromatic418967fa.accept_13_5_11_3_1_902 70 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 211 (accept_3_3 68 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 211 (accept_3_3 65 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 211
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 211 (accept_3_3 62 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 211 (accept_3_3 59 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 211 (accept_3_3 56 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 211 (accept_3_3 53 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 211 (accept_3_3 50 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 211 (accept_3_3 47 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 211
  (Polychromatic418967fa.accept_17_11_13_7_1_3795 45 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 115 211 (accept_3_3 44 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 115 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 211 (Polychromatic418967fa.accept_9_6_7_4_1_212
  42 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 211 (accept_3_3 41
  115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 211 (accept_3_3 38 115 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 211 (Polychromatic418967fa.accept_10_6_5_1_1_482
  36 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 211 (accept_3_3 35
  115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 34 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 115 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 211 (accept_3_3 32 115 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 211 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 211 (accept_3_3 29 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 211 (accept_3_3 26 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 211 (accept_3_3 23 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 211 (accept_3_3 20 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 211 (accept_3_3 17 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 211 (accept_3_3 14 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 115 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 211 (accept_3_3 11 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 211 (accept_3_3 8 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 211 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 211 (accept_3_3 5 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 211 (accept_3_3 2 115 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  114 211 (Eq.refl Bool.true) (allA_succ_of_accept 97 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 211
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 96 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 114 211 (accept_3_3 95 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 211 (accept_3_3 92 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 114 211 (accept_3_3 89 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 211 (accept_3_3 86 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 211 (accept_3_3 83 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 211 (accept_3_3 80 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 211
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 78 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 114 211 (accept_3_3 77 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 114 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 114 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 211 (accept_3_3 74 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 211
  (Polychromatic418967fa.accept_11_6_4_2_1_599 72 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 114 211 (accept_3_3 71 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 211 (accept_3_3 68 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 211 (accept_3_3 65 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 211 (accept_3_3 62 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 211
  (Polychromatic418967fa.accept_21_18_9_1_1_9467 60 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 211 (accept_3_3 59 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 114 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 58 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 211 (accept_3_3 56 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 211
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 211 (accept_3_3 53 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 211 (accept_3_3 50 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 211 (accept_3_3 47 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 211 (accept_3_3 44 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 211
  (Polychromatic418967fa.accept_11_9_4_2_1_600 42 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 211 (accept_3_3 41 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 211 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 211 (accept_3_3 38 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 211
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 211 (accept_3_3 35 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 211 (accept_3_3 32 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 211 (accept_3_3 29 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 211 (accept_3_3 26 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 211 (accept_3_3 23 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 211 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 211 (accept_3_3 20 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 211
  (Polychromatic418967fa.accept_21_18_9_1_1_9467 18 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 211 (accept_3_3 17 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 211 (accept_3_3 14 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 211 (accept_3_3 11 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 211 (accept_3_3 8 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 211 (accept_3_3 5 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 211 (Polychromatic418967fa.accept_17_4_12_7_1_8771 4 114 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 211 (accept_3_3 2 114 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  113 211 (Eq.refl Bool.true) (allA_of_3_1 99 113 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 112 211
  (Eq.refl Bool.true) (allA_succ_of_accept 99 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 211 (accept_3_3 98 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 211 (Polychromatic418967fa.accept_18_7_4_13_1_3315 97 112
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 96 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 112 211 (accept_3_3 95 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 211 (accept_3_3 92 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 211 (Polychromatic418967fa.accept_19_15_17_2_1_4097 91 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 211
  (Polychromatic418967fa.accept_19_14_17_2_1_1720 90 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 112 211 (accept_3_3 89 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 112 211 (Polychromatic418967fa.accept_17_3_10_7_1_2646 88 112 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 211 (accept_3_3 86 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 211 (Polychromatic418967fa.accept_13_7_8_3_1_1533
  85 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 112 211
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 84 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 112 211 (accept_3_3 83 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 211 (accept_3_3 80 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 79 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 112 211
  (Polychromatic418967fa.accept_21_15_7_1_1_6326 78 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 112 211 (accept_3_3 77 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 112 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 112 211 (accept_3_3 74 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 112 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 112 211
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 112 211 (accept_3_3 71 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 211 (accept_3_3 68 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 112 211 (Polychromatic418967fa.accept_17_16_10_7_1_2671 67 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 112 211 (accept_3_3 65 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 64 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 211 (accept_3_3 62 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 61 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 211
  (Polychromatic418967fa.accept_19_3_17_2_1_6963 60 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 112 211 (accept_3_3 59 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 112 211 (accept_3_3 56 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 112 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 211
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 112 211 (accept_3_3 53 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 112 211 (Polychromatic418967fa.accept_17_1_10_7_1_12461 52 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 211 (accept_3_3 50 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 112 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 211
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 211 (accept_3_3 47 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 211 (accept_3_3 44 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 211
  (Polychromatic418967fa.accept_19_4_17_2_1_5409 42 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 211 (accept_3_3 41 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 211 (accept_3_3 38 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 211 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 112 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 211 (accept_3_3 35 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 211 (accept_3_3 32 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 211
  (Polychromatic418967fa.accept_22_8_2_13_1_10950 30 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 112 211 (accept_3_3 29 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 112 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 28 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27
  112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 211 (accept_3_3 26
  112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 211
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 112 211 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 112 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 211 (accept_3_3 23 112 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 211 (accept_3_3 20 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 211 (accept_3_3 17 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 112
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 211 (accept_3_3 14 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 211 (Polychromatic418967fa.accept_19_12_17_2_1_6888 12 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 211 (accept_3_3 11 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 211 (accept_3_3 8 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 211 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 211 (accept_3_3 5 112 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 211 (Polychromatic418967fa.accept_19_4_17_2_1_5409 4 112 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 211 (accept_3_3 2 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 211 (Polychromatic418967fa.accept_17_1_10_7_1_12461 1 112 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 111 211 (Eq.refl Bool.true) (allA_succ_of_accept 100 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 111 211
  (Polychromatic418967fa.accept_13_8_7_3_1_430 99 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 111 211 (accept_3_3 98 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 111 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 111 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 211 (accept_3_3 95 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 111 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 111 211 (accept_3_3 92 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 111 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 111 211 (Polychromatic418967fa.accept_17_5_9_7_1_6185 90 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 211 (accept_3_3 89 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 111 211 (accept_3_3 86 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 111 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 85 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 111 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 211 (accept_3_3 83 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 111 211 (accept_3_3 80 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 111 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 111 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 211 (accept_3_3 77 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 111 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 111 211 (accept_3_3 74 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 111 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 111 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 211 (accept_3_3 71 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 111 211 (accept_3_3 68 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 111 211 (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 111 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 66 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 211 (accept_3_3 65 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 211
  (Polychromatic418967fa.accept_13_11_7_3_1_894 63 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 111 211 (accept_3_3 62 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 111 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 111 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 211 (accept_3_3 59 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 211 (accept_3_3 56 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 211 (accept_3_3 53 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 211 (accept_3_3 50 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 211 (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 211 (accept_3_3 47 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 211 (accept_3_3 44 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 211 (accept_3_3 41 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 211
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 211 (accept_3_3 38 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 211 (accept_3_3 35 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 211 (accept_3_3 32 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 211 (Polychromatic418967fa.accept_22_9_1_13_1_7731 31 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 211 (accept_3_3 29 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 211
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 211 (accept_3_3 26 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 211 (accept_3_3 23 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 211
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 211 (accept_3_3 20 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 211 (accept_3_3 17 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 211 (accept_3_3 14 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 211 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 211 (accept_3_3 11 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 211 (accept_3_3 8 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 211 (accept_3_3 5 111 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 211
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 211 (accept_3_3 2 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 111 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 110 211 (Eq.refl Bool.true) (allA_of_3_1 102 110 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 109
  211 (Eq.refl Bool.true) (allA_succ_of_accept 102 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 211 (accept_3_3 101 109 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 211 (Polychromatic418967fa.accept_11_1_10_2_1_58
  100 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 211
  (Polychromatic418967fa.accept_13_8_5_3_1_427 99 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 211 (accept_3_3 98 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 211 (accept_3_3 95 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 211 (accept_3_3 92 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 211 (Polychromatic418967fa.accept_21_7_4_1_1_3300 91 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 211 (accept_3_3 89 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 211 (accept_3_3 86 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 211 (accept_3_3 83 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 211
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 81 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 211 (accept_3_3 80 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 211 (accept_3_3 77 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 211 (Polychromatic418967fa.accept_13_11_5_3_1_889 76 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 211 (accept_3_3 74 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 211 (accept_3_3 71 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 69 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 211 (accept_3_3 68 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 211 (accept_3_3 65 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 211 (Polychromatic418967fa.accept_18_10_1_13_1_2192 64 109 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 211
  (Polychromatic418967fa.accept_13_11_5_3_1_889 63 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 211 (accept_3_3 62 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 211 (accept_3_3 59 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 211 (accept_3_3 56 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 211 (accept_3_3 53 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 211 (accept_3_3 50 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 211 (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 211 (accept_3_3 47 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 211 (accept_3_3 44 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 211 (accept_3_3 41 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 211 (accept_3_3 38 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 211 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 211 (Polychromatic418967fa.accept_19_17_14_2_1_4116 36 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 211 (accept_3_3 35 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 211 (accept_3_3 32 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 211 (accept_3_3 29 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 211
  (Polychromatic418967fa.accept_13_1_5_3_1_888 27 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 211 (accept_3_3 26 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 211 (accept_3_3 23 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 211 (accept_3_3 20 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 211 (accept_3_3 17 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 211 (accept_3_3 14 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 211 (Polychromatic418967fa.accept_21_13_4_1_1_942 13 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 211 (accept_3_3 11 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 211
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 211 (accept_3_3 8 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 211 (accept_3_3 5 109 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 211 (Polychromatic418967fa.accept_14_4_11_1_1_940 4 109 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 211 (accept_3_3 2 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 109 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 108 211 (Eq.refl Bool.true) (allA_succ_of_accept 103 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 108
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 108 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 102 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 108 211 (accept_3_3 101 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 108 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 99 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 211 (accept_3_3 98 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 211 (Polychromatic418967fa.accept_20_17_8_11_1_6615 97 108
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 108 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 108 211 (accept_3_3 95 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 108 211 (Polychromatic418967fa.accept_15_4_3_1_1_487 94 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 211 (accept_3_3 92 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 211 (Polychromatic418967fa.accept_19_15_13_2_1_6851 91 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 211
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 90 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 108 211 (accept_3_3 89 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 108 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 211 (accept_3_3 86 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 85 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 211
  (Polychromatic418967fa.accept_11_7_9_2_1_260 84 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 108 211 (accept_3_3 83 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 211 (accept_3_3 80 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 211
  (Polychromatic418967fa.accept_20_18_8_11_1_9699 78 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 211 (accept_3_3 77 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 108 211 (Polychromatic418967fa.accept_23_7_16_4_1_12508 76 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424
  75 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 211 (accept_3_3 74
  108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 211
  (Polychromatic418967fa.accept_10_3_8_1_1_182 73 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 108 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 211 (accept_3_3 71 108 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 108 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 211
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 108 211 (accept_3_3 68 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 108 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 66 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 211 (accept_3_3 65 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 64 108
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 211
  (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 108 211 (accept_3_3 62 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 211 (accept_3_3 59 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 211
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 57 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 108 211 (accept_3_3 56 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 108 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 211 (accept_3_3 53 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 211 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 211 (accept_3_3 50 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 108 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 211 (accept_3_3 47 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 211
  (Polychromatic418967fa.accept_19_7_13_2_1_2878 45 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 211 (accept_3_3 44 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 108 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 211 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 211 (accept_3_3 41 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 211 (accept_3_3 38 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 211 (accept_3_3 35 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 211 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 108
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 211 (accept_3_3 32 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 211 (accept_3_3 29 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 211 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 211
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 211 (accept_3_3 26 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 211 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 211 (accept_3_3 23 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 211 (Polychromatic418967fa.accept_25_22_8_11_1_12507 22
  108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 211 (accept_3_3 20 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 211 (accept_3_3 17 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 211
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 211 (accept_3_3 14 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 211 (accept_3_3 11 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 211 (Polychromatic418967fa.accept_16_10_12_3_1_4252 10 108 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 211 (accept_3_3 8 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 211 (accept_3_3 5 108 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 211
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 211 (accept_3_3 2 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 108 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 107 211 (Eq.refl Bool.true) (allA_of_3_1 105 107 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 106 211 (allA_succ_of_accept 105 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 211 (accept_3_3 104 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 106 211 (Polychromatic418967fa.accept_13_12_2_3_1_1527 103
  106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 211 (accept_3_3 101 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 211 (accept_3_3 98 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 211 (accept_3_3 95 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 211 (Polychromatic418967fa.accept_20_14_6_11_1_6600 94 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 211 (accept_3_3 92 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 211
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 90 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 211 (accept_3_3 89 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 211 (accept_3_3 86 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 211 (accept_3_3 83 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 211 (accept_3_3 80 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 79 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 211 (accept_3_3 77 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 211 (accept_3_3 74 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 211 (accept_3_3 71 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 211 (Polychromatic418967fa.accept_13_5_2_3_1_1526 70 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 211 (accept_3_3 68 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 67 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 211 (accept_3_3 65 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 211 (accept_3_3 62 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 211 (accept_3_3 59 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 211 (Polychromatic418967fa.accept_14_2_8_1_1_1647 58 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 211 (accept_3_3 56 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 211
  (Polychromatic418967fa.accept_17_3_4_7_1_1658 54 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 211 (accept_3_3 53 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 211 (accept_3_3 50 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 211 (accept_3_3 47 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 211 (accept_3_3 44 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 211 (Polychromatic418967fa.accept_25_18_6_11_1_12487 43 106 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 211 (accept_3_3 41 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 211 (accept_3_3 38 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 211
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 211 (accept_3_3 35 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 211 (Polychromatic418967fa.accept_19_15_11_2_1_12506 34 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 211 (accept_3_3 32 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 106
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 211 (accept_3_3 29 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 211 (accept_3_3 26 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 211 (accept_3_3 23 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 211 (accept_3_3 20 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 211
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 211 (accept_3_3 17 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 211 (accept_3_3 14 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 211 (accept_3_3 11 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 211 (accept_3_3 8 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 211 (accept_3_3 5 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 106 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 211 (accept_3_3 2 106 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 211 (allA_succ_of_accept 104 105 211 (accept_3_3 104 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 103 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 211 (accept_3_3 101 105
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 211
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 211 (accept_3_3 98 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 211 (Polychromatic418967fa.accept_10_6_5_1_1_482
  96 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 211 (accept_3_3 95
  105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 211 (accept_3_3 92 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 90
  105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 211 (accept_3_3 89
  105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 211
  (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 105 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 211 (accept_3_3 86 105 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 105 211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 85 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 211 (accept_3_3 83 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 211 (accept_3_3 80 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 211 (accept_3_3 77 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 211 (accept_3_3 74 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 211
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 211 (accept_3_3 71 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 211 (accept_3_3 68 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 67 105
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 211 (accept_3_3 65 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 211 (accept_3_3 62 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 105 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 211
  (Polychromatic418967fa.accept_16_12_9_3_1_5363 60 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 211 (accept_3_3 59 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 211 (accept_3_3 56 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 211 (accept_3_3 53 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 211 (accept_3_3 50 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 105
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 211 (accept_3_3 47 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 211 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 211 (accept_3_3 44 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 211 (accept_3_3 41 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 211 (accept_3_3 38 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 211
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 211 (accept_3_3 35 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 211 (accept_3_3 32 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 105
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 211 (accept_3_3 29 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 211 (accept_3_3 26 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 211 (accept_3_3 23 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 211 (accept_3_3 20 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 211 (accept_3_3 17 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 211 (accept_3_3 14 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 105 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 211 (accept_3_3 11 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 211 (accept_3_3 8 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 211 (accept_3_3 5 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 211 (accept_3_3 2 105 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 211 (allA_of_3_1 104 104 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 211
  (allA_succ_of_accept 102 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 103 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 211 (accept_3_3 101 103 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 211
  (Polychromatic418967fa.accept_21_15_19_1_1_12505 99 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 103 211 (accept_3_3 98 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 103 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 103 211 (Polychromatic418967fa.accept_17_11_1_7_1_2657 96 103
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 211 (accept_3_3 95 103
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 94 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 103 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 93 103 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 103 211 (accept_3_3 92 103 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 103 211 (Polychromatic418967fa.accept_16_11_7_3_1_3163 91 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 103 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 103 211 (accept_3_3 89 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 103 211 (accept_3_3 86 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 103 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 103 211 (accept_3_3 83 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 103 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 82 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 211 (accept_3_3 80 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 211 (Polychromatic418967fa.accept_16_15_7_3_1_4273 79 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 211
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 211 (accept_3_3 77 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 211 (accept_3_3 74 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 211
  (Polychromatic418967fa.accept_10_2_3_1_1_481 72 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 211 (accept_3_3 71 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 211 (accept_3_3 68 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 211 (accept_3_3 65 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 211 (Polychromatic418967fa.accept_15_3_13_1_1_479 63 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 211 (accept_3_3 62 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 211 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 103
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 211 (accept_3_3 59 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 211 (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 211 (accept_3_3 56 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 211
  (Polychromatic418967fa.accept_13_2_12_3_1_415 54 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 211 (accept_3_3 53 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 211 (Polychromatic418967fa.accept_19_13_8_2_1_4089 51 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 211 (accept_3_3 50 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 211 (Polychromatic418967fa.accept_19_11_8_2_1_2847 49 103
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 211 (accept_3_3 47 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 211 (accept_3_3 44 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 211 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 211
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 211 (accept_3_3 41 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 211 (accept_3_3 38 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 211 (Polychromatic418967fa.accept_21_16_19_1_1_6320 37 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 211 (accept_3_3 35 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 211 (Polychromatic418967fa.accept_15_3_13_1_1_479 33 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 211 (accept_3_3 32 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 211
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 211 (accept_3_3 29 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 211 (accept_3_3 26 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 211 (accept_3_3 23 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 211 (Polychromatic418967fa.accept_26_21_25_3_1_12504 21 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 211 (accept_3_3 20 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 211 (Polychromatic418967fa.accept_25_19_3_11_1_12503 19
  103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 211 (accept_3_3 17 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 211 (Polychromatic418967fa.accept_21_16_19_1_1_6320 16 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 211 (accept_3_3 14 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 211 (accept_3_3 11 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 211 (accept_3_3 8 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 211 (Polychromatic418967fa.accept_21_7_19_1_1_9497 7 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 211 (accept_3_3 5 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 211 (accept_3_3 2 103 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 211 (Polychromatic418967fa.accept_19_1_8_2_1_2876 1 103 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 211 (allA_succ_of_accept 101 102 211 (accept_3_3 101 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 102 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 99 102
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 211 (accept_3_3 98 102
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9
  97 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 96 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 211 (accept_3_3 95 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 211 (accept_3_3 92 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 211
  (Polychromatic418967fa.accept_19_14_7_2_1_11116 90 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 102 211 (accept_3_3 89 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 102 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 211 (accept_3_3 86 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 211
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 84 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 211 (accept_3_3 83 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 211 (accept_3_3 80 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 211 (accept_3_3 77 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 211 (accept_3_3 74 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 211
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 211 (accept_3_3 71 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 211 (accept_3_3 68 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 211 (accept_3_3 65 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 211 (accept_3_3 62 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 211 (accept_3_3 59 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 211 (accept_3_3 56 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 211 (accept_3_3 53 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 211 (accept_3_3 50 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 211
  (Polychromatic418967fa.accept_22_4_14_13_1_5977 48 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 211 (accept_3_3 47 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 211 (accept_3_3 44 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218
  43 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 211 (accept_3_3 41 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 211 (accept_3_3 38 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 211 (accept_3_3 35 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 211 (accept_3_3 32 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 211
  (Polychromatic418967fa.accept_21_9_18_1_1_9424 30 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 211 (accept_3_3 29 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 211 (accept_3_3 26 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 211 (accept_3_3 23 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 211 (Polychromatic418967fa.accept_25_22_2_11_1_12502 22 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 211 (accept_3_3 20 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 211
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 211 (accept_3_3 17 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 211 (accept_3_3 14 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 211 (accept_3_3 11 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 211 (accept_3_3 8 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 211 (accept_3_3 5 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 102 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 211 (accept_3_3 2 102 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 211 (allA_of_3_1 101 101 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 211 (allA_succ_of_accept 99
  100 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 211 (accept_3_3 98 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 100 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 211 (accept_3_3 95 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225
  94 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 211 (accept_3_3 92 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 211 (accept_3_3 89 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 211 (accept_3_3 86 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 100 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 85 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 100 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 211 (accept_3_3 83 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 211 (accept_3_3 80 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 211 (accept_3_3 77 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 211 (accept_3_3 74 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 211 (accept_3_3 71 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 211 (accept_3_3 68 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 211 (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 211 (accept_3_3 65 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 211 (Polychromatic418967fa.accept_13_12_9_3_1_3047 64 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 211 (accept_3_3 62 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 211 (accept_3_3 59 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 211 (accept_3_3 56 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 211 (accept_3_3 53 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 211 (accept_3_3 50 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 211 (Polychromatic418967fa.accept_16_1_4_3_1_3148 49 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 211 (accept_3_3 47 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 211 (accept_3_3 44 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 211 (accept_3_3 41 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 211 (Polychromatic418967fa.accept_16_8_4_3_1_3146 40 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 211 (accept_3_3 38 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 211 (accept_3_3 35 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 211 (accept_3_3 32 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 211 (accept_3_3 29 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 211 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 211 (accept_3_3 26 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 211 (accept_3_3 23 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 211 (accept_3_3 20 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 211 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 211 (accept_3_3 17 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 211 (accept_3_3 14 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 211 (accept_3_3 11 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 211 (accept_3_3 8 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 211 (accept_3_3 5 100 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 211 (Polychromatic418967fa.accept_18_4_10_13_1_5883 4 100 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 211 (accept_3_3 2 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 211 (Polychromatic418967fa.accept_16_1_4_3_1_3148 1 100 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  211 (allA_succ_of_accept 98 99 211 (accept_3_3 98 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 211 (Polychromatic418967fa.accept_15_7_9_1_1_473 97 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 96 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 211 (accept_3_3 95 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 211 (accept_3_3 92 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 211 (Polychromatic418967fa.accept_17_6_14_7_1_6115 91 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 211 (Polychromatic418967fa.accept_19_14_4_2_1_2840 90 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 211 (accept_3_3 89 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 211
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 87 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 211 (accept_3_3 86 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 211 (Polychromatic418967fa.accept_26_6_21_3_1_12501 84 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 211 (accept_3_3 83 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 211 (accept_3_3 80 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 211 (Polychromatic418967fa.accept_21_16_15_1_1_12500 79 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 211 (accept_3_3 77 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 75 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 211 (accept_3_3 74 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 211 (Polychromatic418967fa.accept_19_16_4_2_1_4102 73 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 211 (accept_3_3 71 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 211 (accept_3_3 68 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 211 (Polychromatic418967fa.accept_15_7_9_1_1_473 67 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 66 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 211 (accept_3_3 65 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 211
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 211 (accept_3_3 62 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 61 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 211 (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 211 (accept_3_3 59 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 211 (accept_3_3 56 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 211 (Polychromatic418967fa.accept_19_16_4_2_1_4102 54 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 211 (accept_3_3 53 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 211
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 211 (accept_3_3 50 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 211 (Polychromatic418967fa.accept_19_11_4_2_1_1700 49 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 211 (accept_3_3 47 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 211 (accept_3_3 44 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 211 (Polychromatic418967fa.accept_19_5_4_2_1_6840 43 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 211 (accept_3_3 41 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 39 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 211 (accept_3_3 38 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 211 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 211 (accept_3_3 35 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 211 (accept_3_3 32 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 211 (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 211 (accept_3_3 29 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 211
  (Polychromatic418967fa.accept_17_10_14_7_1_2679 27 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 211 (accept_3_3 26 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 211 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 211 (accept_3_3 23 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 211 (accept_3_3 20 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 211 (Polychromatic418967fa.accept_21_19_15_1_1_6345 19 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 211 (accept_3_3 17 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 211 (accept_3_3 14 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 211 (Polychromatic418967fa.accept_25_13_24_11_1_12499 13 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 211 (accept_3_3 11 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 211 (accept_3_3 8 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  211 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 211 (accept_3_3 5 99 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 211 (accept_3_3 2 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  211 (Polychromatic418967fa.accept_24_1_3_19_1_9038 1 99 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  211 (allA_of_3_1 98 98 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 211 (allA_succ_of_accept 96 97 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 96 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 211 (accept_3_3 95 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 211 (accept_3_3 92 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 211 (accept_3_3 89 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 88 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 211 (accept_3_3 86 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 85 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 211 (accept_3_3 83 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 211 (accept_3_3 80 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 211 (accept_3_3 77 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 76 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 211 (accept_3_3 74 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 211 (accept_3_3 71 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 211 (accept_3_3 68 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 211 (Polychromatic418967fa.accept_21_4_13_1_1_12498 67 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 211 (accept_3_3 65 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 211 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 211 (accept_3_3 62 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 211 (accept_3_3 59 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 211 (accept_3_3 56 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 211 (accept_3_3 53 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 211 (Polychromatic418967fa.accept_16_4_1_3_1_6581 52 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 211 (accept_3_3 50 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 211 (accept_3_3 47 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 211 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 211 (accept_3_3 44 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 211 (Polychromatic418967fa.accept_22_21_9_13_1_12497 43 97
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 211 (accept_3_3 41 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 211 (accept_3_3 38 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 211
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 211 (accept_3_3 35 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 211 (accept_3_3 32 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 31 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 211 (accept_3_3 29 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 211 (accept_3_3 26 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 211 (accept_3_3 23 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 211 (accept_3_3 20 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 211 (accept_3_3 17 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 211 (accept_3_3 14 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 211 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 211 (accept_3_3 11 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 211 (accept_3_3 8 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 211 (accept_3_3 5 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  211 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 97 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 211 (accept_3_3 2 97 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 211
  (allA_succ_of_accept 95 96 211 (accept_3_3 95 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 211 (accept_3_3 92 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 211 (accept_3_3 89 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 211 (accept_3_3 86 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 85 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 211 (accept_3_3 83 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 211 (accept_3_3 80 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 78 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 211 (accept_3_3 77 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 211 (accept_3_3 74 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 211 (accept_3_3 71 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 211 (accept_3_3 68 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 211 (accept_3_3 65 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 211 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 211 (accept_3_3 62 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 211 (accept_3_3 59 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 211 (Polychromatic418967fa.accept_13_6_5_3_1_426 58 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 211 (accept_3_3 56 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 211
  (Polychromatic418967fa.accept_13_2_5_3_1_406 54 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 211 (accept_3_3 53 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 211 (Polychromatic418967fa.accept_19_13_1_2_1_11154 51 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 211 (accept_3_3 50 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 96 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 211 (accept_3_3 47 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 211 (accept_3_3 44 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 211 (accept_3_3 41 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 211 (Polychromatic418967fa.accept_13_1_5_3_1_888 40 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 211 (accept_3_3 38 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 211
  (Polychromatic418967fa.accept_21_15_12_1_1_9491 36 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 211 (accept_3_3 35 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 211 (accept_3_3 32 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 211 (accept_3_3 29 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 211 (accept_3_3 26 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 211 (accept_3_3 23 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 211 (accept_3_3 20 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 211 (accept_3_3 17 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 211 (accept_3_3 14 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 211 (accept_3_3 11 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 211 (accept_3_3 8 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 211 (accept_3_3 5 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 211 (accept_3_3 2 96 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 211
  (allA_of_3_1 95 95 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 211 (allA_succ_of_accept 93 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 211 (accept_3_3 92 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 211 (Polychromatic418967fa.accept_16_11_14_3_1_3140 91 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 211 (Polychromatic418967fa.accept_17_5_9_7_1_6185 90 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 211 (accept_3_3 89 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 211 (accept_3_3 86 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 211 (Polychromatic418967fa.accept_22_18_6_13_1_7751 84 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 211 (accept_3_3 83 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 94 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 211 (accept_3_3 80 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 211 (Polychromatic418967fa.accept_15_3_4_1_1_1072 78 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 211 (accept_3_3 77 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 211 (accept_3_3 74 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 211 (accept_3_3 71 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 211 (accept_3_3 68 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 211 (Polychromatic418967fa.accept_17_15_9_7_1_3816 66 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 211 (accept_3_3 65 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 94 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 211 (accept_3_3 62 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 211 (accept_3_3 59 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 211 (accept_3_3 56 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 211 (accept_3_3 53 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 211 (accept_3_3 50 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 211 (accept_3_3 47 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 211 (accept_3_3 44 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 211 (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 211 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 211 (accept_3_3 41 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 94 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 211 (accept_3_3 38 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 211 (Polychromatic418967fa.accept_17_2_9_7_1_5002 36 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 211 (accept_3_3 35 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 211 (Polychromatic418967fa.accept_19_15_18_2_1_6857 34 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 211 (accept_3_3 32 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 211 (Polychromatic418967fa.accept_22_9_6_13_1_12496 31 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 211 (accept_3_3 29 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 211 (accept_3_3 26 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 211 (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 211 (accept_3_3 23 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 211 (Polychromatic418967fa.accept_17_5_9_7_1_6185 22 94 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 211 (accept_3_3 20 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 211 (accept_3_3 17 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 211 (accept_3_3 14 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 211 (accept_3_3 11 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 211 (accept_3_3 8 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 94 211 (Polychromatic418967fa.accept_20_6_14_11_1_6537 6 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 211 (accept_3_3 5 94 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 211 (accept_3_3 2 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 93 211 (allA_succ_of_accept 92 93 211 (accept_3_3 92 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 93 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 211 (accept_3_3 89 93 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 88
  93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 211 (accept_3_3 86 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 211 (Polychromatic418967fa.accept_17_16_8_7_1_4983 84 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 211 (accept_3_3 83 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 211 (accept_3_3 80 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 211 (accept_3_3 77 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 211 (accept_3_3 74 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 211 (accept_3_3 71 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 211 (accept_3_3 68 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 211 (Polychromatic418967fa.accept_17_16_8_7_1_4983 67 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 211 (accept_3_3 65 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 211
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 211 (accept_3_3 62 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 211 (accept_3_3 59 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 211
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 211 (accept_3_3 56 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 211 (accept_3_3 53 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 211 (accept_3_3 50 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 211 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 211 (accept_3_3 47 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 211 (accept_3_3 44 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 211 (accept_3_3 41 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 211 (accept_3_3 38 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 211 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 211 (accept_3_3 35 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 211 (accept_3_3 32 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 211 (accept_3_3 29 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 211 (accept_3_3 26 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 211 (accept_3_3 23 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 211 (accept_3_3 20 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 211 (accept_3_3 17 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 211 (accept_3_3 14 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 211 (accept_3_3 11 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 211
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 211 (accept_3_3 8 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 211 (accept_3_3 5 93 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  93 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 211 (accept_3_3 2 93 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 93
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 211
  (allA_of_3_1 92 92 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 211 (allA_succ_of_accept 90 91 211
  (Polychromatic418967fa.accept_14_6_7_1_1_78 90 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 211 (accept_3_3 89 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 211 (accept_3_3 86 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 211 (Polychromatic418967fa.accept_19_9_15_2_1_9758 85 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 211 (accept_3_3 83 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 211 (Polychromatic418967fa.accept_17_14_6_7_1_4980 82 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 211 (Polychromatic418967fa.accept_17_13_6_7_1_4999 81 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 211 (accept_3_3 80 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 211 (accept_3_3 77 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 211 (Polychromatic418967fa.accept_14_6_7_1_1_78 76 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 211 (accept_3_3 74 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 211 (Polychromatic418967fa.accept_21_10_7_1_1_9464 73 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 211
  (Polychromatic418967fa.accept_16_8_11_3_1_4279 72 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 211 (accept_3_3 71 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 211 (accept_3_3 68 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 211 (accept_3_3 65 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 211 (Polychromatic418967fa.accept_14_8_7_1_1_1615 64 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 211 (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 211 (accept_3_3 62 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 211 (accept_3_3 59 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 211 (Polychromatic418967fa.accept_19_1_15_2_1_6950 58 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 211 (accept_3_3 56 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 211
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 211 (accept_3_3 53 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 211 (accept_3_3 50 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 211 (Polychromatic418967fa.accept_19_11_15_2_1_4096 49 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 211 (accept_3_3 47 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 211 (Polychromatic418967fa.accept_16_14_11_3_1_4249 46 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 211 (accept_3_3 44 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 211 (accept_3_3 41 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 211 (Polychromatic418967fa.accept_16_8_11_3_1_4279 40 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 211 (accept_3_3 38 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 211 (Polychromatic418967fa.accept_19_18_15_2_1_11128 37 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 211
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 211 (accept_3_3 35 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 211 (accept_3_3 32 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 211 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 211 (accept_3_3 29 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 211 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 211 (accept_3_3 26 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 211 (accept_3_3 23 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 211 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 211 (accept_3_3 20 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 211 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 211
  (Polychromatic418967fa.accept_19_18_15_2_1_11128 18 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 91 211 (accept_3_3 17 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 211 (accept_3_3 14 91 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618
  13 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 211 (accept_3_3 11 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 211 (Polychromatic418967fa.accept_18_10_1_13_1_2192 10 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 211 (Polychromatic418967fa.accept_19_9_15_2_1_9758 9 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 211 (accept_3_3 8 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 211 (accept_3_3 5 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  211 (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 91 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 211 (accept_3_3 2 91 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 91 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 211
  (allA_succ_of_accept 89 90 211 (accept_3_3 89 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 211 (Polychromatic418967fa.accept_19_12_14_2_1_1692 88 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 211 (Polychromatic418967fa.accept_13_9_12_3_1_907 87 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 211 (accept_3_3 86 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 211
  (Polychromatic418967fa.accept_19_8_14_2_1_9774 84 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 211 (accept_3_3 83 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 211 (accept_3_3 80 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 211
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 78 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 211 (accept_3_3 77 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 211 (Polychromatic418967fa.accept_16_12_10_3_1_4209 76 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 211 (accept_3_3 74 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 211 (accept_3_3 71 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 211 (Polychromatic418967fa.accept_21_7_6_1_1_11009 70 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 211 (accept_3_3 68 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 67 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 211
  (Polychromatic418967fa.accept_17_15_5_7_1_2694 66 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 211 (accept_3_3 65 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 211 (Polychromatic418967fa.accept_19_7_14_2_1_4095 64 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 211 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 211 (accept_3_3 62 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 211
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 211 (accept_3_3 59 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 211 (accept_3_3 56 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 211 (Polychromatic418967fa.accept_16_7_10_3_1_2210 55 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 211 (accept_3_3 53 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 211 (Polychromatic418967fa.accept_22_8_2_13_1_10950 52 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 211 (accept_3_3 50 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 211
  (Polychromatic418967fa.accept_13_9_12_3_1_907 48 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 211 (accept_3_3 47 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 211 (Polychromatic418967fa.accept_17_12_5_7_1_6179 46 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 211 (accept_3_3 44 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 211 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 211
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 211 (accept_3_3 41 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 211 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 211 (accept_3_3 38 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 211
  (Polychromatic418967fa.accept_19_17_14_2_1_4116 36 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 211 (accept_3_3 35 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 211 (Polychromatic418967fa.accept_20_14_10_11_1_2393 34 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 211 (accept_3_3 32 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 211 (Polychromatic418967fa.accept_19_12_14_2_1_1692 31 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 211 (accept_3_3 29 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 211 (Polychromatic418967fa.accept_19_8_14_2_1_9774 27 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 211 (accept_3_3 26 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 211
  (Polychromatic418967fa.accept_19_5_14_2_1_1716 24 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 211 (accept_3_3 23 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 211 (Polychromatic418967fa.accept_13_9_12_3_1_907 22 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 211 (accept_3_3 20 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 211
  (Polychromatic418967fa.accept_22_18_2_13_1_12495 18 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 211 (accept_3_3 17 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 90 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 211 (accept_3_3 14 90 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 211 (accept_3_3 11 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 211 (Polychromatic418967fa.accept_22_10_2_13_1_5964 10 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 211 (accept_3_3 8 90 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 211 (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 211
  (Polychromatic418967fa.accept_23_6_21_4_1_12494 6 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 211 (accept_3_3 5 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  211 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 90 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 90 211 (Polychromatic418967fa.accept_20_3_10_11_1_12493 3 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 211 (accept_3_3 2 90 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 211
  (allA_of_3_1 89 89 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 211 (allA_succ_of_accept 87 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 211 (accept_3_3 86 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 85 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 211 (accept_3_3 83 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 211 (accept_3_3 80 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 79 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 211 (accept_3_3 77 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 76 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 211 (accept_3_3 74 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 211 (accept_3_3 71 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 211 (accept_3_3 68 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 211 (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 211 (accept_3_3 65 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 211 (accept_3_3 62 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 211 (accept_3_3 59 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 211 (accept_3_3 56 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 211 (accept_3_3 53 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 211 (accept_3_3 50 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 211 (accept_3_3 47 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 211 (accept_3_3 44 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 211 (accept_3_3 41 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 211 (accept_3_3 38 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 211 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 211 (accept_3_3 35 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 211 (accept_3_3 32 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 211 (accept_3_3 29 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 211 (accept_3_3 26 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 211 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 211 (accept_3_3 23 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 211 (accept_3_3 20 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 211 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 211 (accept_3_3 17 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 211 (Polychromatic418967fa.accept_17_16_3_7_1_5028 16 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 211 (accept_3_3 14 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 211 (accept_3_3 11 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 211 (accept_3_3 8 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 211 (accept_3_3 5 88 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 211 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 88 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 211 (accept_3_3 2 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  211 (allA_succ_of_accept 86 87 211 (accept_3_3 86 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 85 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 211 (accept_3_3 83 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 211 (accept_3_3 80 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 211 (accept_3_3 77 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 211 (accept_3_3 74 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 211 (accept_3_3 71 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 211 (accept_3_3 68 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 211 (accept_3_3 65 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 211
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 211 (accept_3_3 62 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 211 (accept_3_3 59 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 211 (accept_3_3 56 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 211 (accept_3_3 53 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 211 (accept_3_3 50 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 211 (accept_3_3 47 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 211
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 211 (accept_3_3 44 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 211 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 211 (accept_3_3 41 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 211 (accept_3_3 38 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 211 (accept_3_3 35 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 211 (accept_3_3 32 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 211 (accept_3_3 29 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 211
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 211 (accept_3_3 26 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 211 (accept_3_3 23 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 211 (accept_3_3 20 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 211 (accept_3_3 17 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 211
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 211 (accept_3_3 14 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 211 (accept_3_3 11 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 211 (accept_3_3 8 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 87 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 211 (accept_3_3 5 87 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 211 (accept_3_3 2 87 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 87
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 211
  (allA_of_3_1 86 86 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 211 (allA_succ_of_accept 84 85 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 84 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 211 (accept_3_3 83 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 211 (accept_3_3 80 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 79 85 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 211 (accept_3_3 77 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 76 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 211 (Polychromatic418967fa.accept_13_10_7_3_1_3041 75 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 211 (accept_3_3 74 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 211 (Polychromatic418967fa.accept_13_8_7_3_1_430 73 85 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 211
  (Polychromatic418967fa.accept_16_8_5_3_1_4297 72 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 211 (accept_3_3 71 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 211 (accept_3_3 68 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 211 (accept_3_3 65 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 211 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 211 (accept_3_3 62 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 211
  (Polychromatic418967fa.accept_11_5_8_2_1_588 60 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 211 (accept_3_3 59 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 211 (Polychromatic418967fa.accept_20_17_5_11_1_9622 57 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 211 (accept_3_3 56 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 211 (Polychromatic418967fa.accept_19_17_9_2_1_12492 55 85
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 211 (accept_3_3 53 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 211 (accept_3_3 50 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 211
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 211 (accept_3_3 47 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 211 (Polychromatic418967fa.accept_19_7_9_2_1_4090 45 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 211 (accept_3_3 44 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 211 (Polychromatic418967fa.accept_13_4_7_3_1_92 43 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 211 (accept_3_3 41 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 211 (accept_3_3 38 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 211 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 211
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 211 (accept_3_3 35 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 211 (Polychromatic418967fa.accept_22_11_19_13_1_9237 33 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 211 (accept_3_3 32 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 211 (Polychromatic418967fa.accept_19_12_9_2_1_11136 31 85
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 211 (accept_3_3 29 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 211 (accept_3_3 26 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 211 (Polychromatic418967fa.accept_23_2_16_4_1_12491 25 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 211 (accept_3_3 23 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 211 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 211 (accept_3_3 20 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 211 (accept_3_3 17 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 211 (Polychromatic418967fa.accept_19_15_9_2_1_8347 15 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 211 (accept_3_3 14 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 211
  (Polychromatic418967fa.accept_19_12_9_2_1_11136 12 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 211 (accept_3_3 11 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 211 (accept_3_3 8 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 211 (accept_3_3 5 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  211 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 85 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 211 (Polychromatic418967fa.accept_29_3_27_8_1_12490 3 85 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 211 (accept_3_3 2 85 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 85 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 211
  (allA_succ_of_accept 83 84 211 (accept_3_3 83 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 211 (accept_3_3 80 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 211 (accept_3_3 77 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 211 (Polychromatic418967fa.accept_16_12_4_3_1_4295 76 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 211 (accept_3_3 74 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 211
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 72 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 211 (accept_3_3 71 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 211 (accept_3_3 68 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 211
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 66 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 211 (accept_3_3 65 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 211 (accept_3_3 62 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 211 (accept_3_3 59 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 211 (Polychromatic418967fa.accept_19_1_8_2_1_2876 58 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 211 (accept_3_3 56 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 211
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 54 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 211 (accept_3_3 53 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 211 (accept_3_3 50 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 211
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 211 (accept_3_3 47 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 211 (accept_3_3 44 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 211 (accept_3_3 41 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 211 (accept_3_3 38 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 211
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 211 (accept_3_3 35 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 211 (accept_3_3 32 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 211
  (Polychromatic418967fa.accept_19_11_8_2_1_2847 30 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 211 (accept_3_3 29 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 211 (accept_3_3 26 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 211 (accept_3_3 23 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 211 (accept_3_3 20 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 211
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 211 (accept_3_3 17 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 211 (accept_3_3 14 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 211 (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 211
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 211 (accept_3_3 11 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 211 (accept_3_3 8 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 211 (accept_3_3 5 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  211 (Polychromatic418967fa.accept_24_4_12_19_1_12489 4 84 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 211 (Polychromatic418967fa.accept_17_3_16_7_1_5014 3 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 211 (accept_3_3 2 84 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 211 (allA_of_3_1
  83 83 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 211 (allA_succ_of_accept 81 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 211 (accept_3_3 80 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 211 (accept_3_3 77 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 211 (accept_3_3 74 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 211 (accept_3_3 71 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 211 (accept_3_3 68 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 211 (accept_3_3 65 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 211 (accept_3_3 62 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 211 (accept_3_3 59 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 211 (Polychromatic418967fa.accept_18_4_10_13_1_5883 58 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 211 (accept_3_3 56 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 211 (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 211 (accept_3_3 53 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 211 (accept_3_3 50 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 211 (accept_3_3 47 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 211 (accept_3_3 44 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 211 (accept_3_3 41 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 211 (accept_3_3 38 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 211 (accept_3_3 35 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 211 (accept_3_3 32 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 211 (accept_3_3 29 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 211 (accept_3_3 26 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 211 (accept_3_3 23 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 211 (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 211 (accept_3_3 20 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 211 (accept_3_3 17 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 211 (accept_3_3 14 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 211 (accept_3_3 11 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 211 (accept_3_3 8 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 211 (accept_3_3 5 82 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 211 (accept_3_3 2 82 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 211
  (allA_succ_of_accept 80 81 211 (accept_3_3 80 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 211 (Polychromatic418967fa.accept_17_11_13_7_1_3795 79 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 211 (accept_3_3 77 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 211 (accept_3_3 74 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 211 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 211 (accept_3_3 71 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 211
  (Polychromatic418967fa.accept_15_9_6_1_1_493 69 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 211 (accept_3_3 68 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 211 (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 211 (accept_3_3 65 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 211 (accept_3_3 62 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 211 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 211 (accept_3_3 59 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 211
  (Polychromatic418967fa.accept_17_6_13_7_1_272 57 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 211 (accept_3_3 56 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 211 (accept_3_3 53 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 211 (accept_3_3 50 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 211 (Polychromatic418967fa.accept_24_1_9_19_1_12488 49 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 211 (accept_3_3 47 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 211 (accept_3_3 44 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 211 (Polychromatic418967fa.accept_25_18_6_11_1_12487 43 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 211 (accept_3_3 41 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 211
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 211 (accept_3_3 38 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 211 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 211 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 211 (accept_3_3 35 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 211 (accept_3_3 32 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 211 (accept_3_3 29 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 211 (accept_3_3 26 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 211 (accept_3_3 23 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 211
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 211 (accept_3_3 20 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 211 (accept_3_3 17 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 211 (accept_3_3 14 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 211 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 211 (accept_3_3 11 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 211
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 211 (accept_3_3 8 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  211 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 211 (accept_3_3 5 81 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 211 (accept_3_3 2 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  211 (Polychromatic418967fa.accept_23_1_12_4_1_12486 1 81 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 211 (allA_of_3_1 80 80 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 211
  (allA_succ_of_accept 78 79 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 211 (accept_3_3 77 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 75
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 211 (accept_3_3 74 79
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 211 (accept_3_3 71 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 70 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 69
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 211 (accept_3_3 68 79
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 211
  (Polychromatic418967fa.accept_13_2_1_3_1_419 67 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 211 (accept_3_3 65 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 211 (Polychromatic418967fa.accept_13_11_1_3_1_910
  63 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 211 (accept_3_3 62
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 211
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 211 (accept_3_3 59 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 58 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 57
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 211 (accept_3_3 56 79
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 79 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 54 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 211 (accept_3_3 53 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 51
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 211 (accept_3_3 50 79
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 211
  (Polychromatic418967fa.accept_19_11_3_2_1_12485 49 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 211 (accept_3_3 47 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 79 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 45
  79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 211 (accept_3_3 44 79
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 211
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 43 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 79 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 211 (accept_3_3 41 79 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 79 211 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 211 (accept_3_3 38 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 211 (accept_3_3 35 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 211 (accept_3_3 32 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 211 (accept_3_3 29 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 211 (accept_3_3 26 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 211 (accept_3_3 23 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 211 (accept_3_3 20 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 211 (accept_3_3 17 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 211 (Polychromatic418967fa.accept_19_16_3_2_1_6964 16 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 211 (accept_3_3 14 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 211 (accept_3_3 11 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 211
  (Polychromatic418967fa.accept_27_9_25_22_1_12484 9 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 211 (accept_3_3 8 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 211 (accept_3_3 5 79 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 211 (accept_3_3 2 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 211
  (allA_succ_of_accept 77 78 211 (accept_3_3 77 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 211 (accept_3_3 74 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 211
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 211 (accept_3_3 71 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 211 (accept_3_3 68 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 211 (Polychromatic418967fa.accept_17_16_10_7_1_2671 67 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 211 (accept_3_3 65 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 211 (accept_3_3 62 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 211
  (Polychromatic418967fa.accept_21_18_15_1_1_9470 60 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 211 (accept_3_3 59 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 211 (accept_3_3 56 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 211
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 211 (accept_3_3 53 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 211 (Polychromatic418967fa.accept_14_9_8_1_1_2381 51 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 211 (accept_3_3 50 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 211 (accept_3_3 47 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 211 (accept_3_3 44 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 211
  (Polychromatic418967fa.accept_23_19_9_4_1_12483 42 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 211 (accept_3_3 41 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 211 (Polychromatic418967fa.accept_21_19_15_1_1_6345 40 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 211 (accept_3_3 38 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 211
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 211 (accept_3_3 35 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 211 (accept_3_3 32 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 211 (Polychromatic418967fa.accept_17_14_10_7_1_2670 31 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 211 (accept_3_3 29 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 211 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 211 (accept_3_3 26 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 211
  (Polychromatic418967fa.accept_21_3_15_1_1_2046 24 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 211 (accept_3_3 23 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 211 (Polychromatic418967fa.accept_29_22_20_8_1_12482 22 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 211 (accept_3_3 20 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 211
  (Polychromatic418967fa.accept_17_1_10_7_1_12461 18 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 211 (accept_3_3 17 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 211 (Polychromatic418967fa.accept_25_15_3_11_1_12481 15 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 211 (accept_3_3 14 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 211 (accept_3_3 11 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 211 (accept_3_3 8 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 211 (accept_3_3 5 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  211 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 78 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 211 (accept_3_3 2 78 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 211 (allA_of_3_1 77 77
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 211 (allA_succ_of_accept 75 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 211 (accept_3_3 74 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 211 (Polychromatic418967fa.accept_13_8_11_3_1_3053 73 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 211 (accept_3_3 71 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 211 (accept_3_3 68 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 67 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 66 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 211 (accept_3_3 65 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 64 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 211 (accept_3_3 62 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 211 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 211 (accept_3_3 59 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 76 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 211 (accept_3_3 56 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 211 (accept_3_3 53 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 211 (accept_3_3 50 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 211 (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 211 (Polychromatic418967fa.accept_17_14_8_7_1_6183 48 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 211 (accept_3_3 47 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 76 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 211 (accept_3_3 44 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 211 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 211 (accept_3_3 41 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 211 (accept_3_3 38 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 211 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 211 (accept_3_3 35 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 76 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 211 (accept_3_3 32 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 211 (accept_3_3 29 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 211 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 211 (accept_3_3 26 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 211 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 211 (accept_3_3 23 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 211 (accept_3_3 20 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 211 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 211 (accept_3_3 17 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 211 (accept_3_3 14 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 211 (Polychromatic418967fa.accept_28_13_20_15_1_12480 13 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 211 (accept_3_3 11 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 211 (accept_3_3 8 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 211 (Polychromatic418967fa.accept_20_6_16_11_1_2379 6 76 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 211 (accept_3_3 5 76 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 211 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 76 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 211 (accept_3_3 2 76 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 1
  76 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 211 (allA_succ_of_accept
  74 75 211 (accept_3_3 74 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 211 (accept_3_3 71 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 69
  75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 211 (accept_3_3 68 75
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 211 (accept_3_3 65 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 211
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 211 (accept_3_3 62 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 211 (accept_3_3 59 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 211 (accept_3_3 56 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 211 (accept_3_3 53 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 211 (accept_3_3 50 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 211 (accept_3_3 47 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 211 (accept_3_3 44 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 211 (accept_3_3 41 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 211 (accept_3_3 38 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 211 (accept_3_3 35 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 211 (accept_3_3 32 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 211 (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 211 (accept_3_3 29 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 211 (accept_3_3 26 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 211 (accept_3_3 23 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 211 (accept_3_3 20 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 211 (accept_3_3 17 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 211 (accept_3_3 14 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 211 (Polychromatic418967fa.accept_18_12_3_13_1_4494 12 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 211 (accept_3_3 11 75 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 211 (accept_3_3 8 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 211 (accept_3_3 5 75 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 211 (accept_3_3 2 75 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 75
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 211 (allA_of_3_1 74 74
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 211 (allA_succ_of_accept 72 73 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 211 (accept_3_3 71 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 211 (accept_3_3 68 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 211 (accept_3_3 65 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 211 (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 211 (accept_3_3 62 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 211 (accept_3_3 59 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 211 (accept_3_3 56 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 211 (accept_3_3 53 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 211 (accept_3_3 50 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 211 (Polychromatic418967fa.accept_17_15_5_7_1_2694 49 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 211 (accept_3_3 47 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 211 (Polychromatic418967fa.accept_17_11_5_7_1_6177 45 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 211 (accept_3_3 44 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 211 (accept_3_3 41 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 211 (accept_3_3 38 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 211
  (Polychromatic418967fa.accept_19_17_16_2_1_8390 36 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 211 (accept_3_3 35 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 211 (accept_3_3 32 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 211 (accept_3_3 29 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 211 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 211 (accept_3_3 26 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 211 (accept_3_3 23 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 211 (accept_3_3 20 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 211 (accept_3_3 17 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 211 (accept_3_3 14 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 211 (Polychromatic418967fa.accept_19_13_16_2_1_11119 13 73 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 211 (accept_3_3 11 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 211 (accept_3_3 8 73 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 211 (accept_3_3 5 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 211 (accept_3_3 2 73 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 211 (Polychromatic418967fa.accept_27_1_19_22_1_12479 1 73 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 211 (allA_succ_of_accept 71
  72 211 (accept_3_3 71 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 211
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 211 (accept_3_3 68 72 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 211 (Polychromatic418967fa.accept_27_13_18_22_1_12478 67 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 211 (accept_3_3 65 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 211 (Polychromatic418967fa.accept_14_8_2_1_1_1652 64 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 211 (accept_3_3 62 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 211
  (Polychromatic418967fa.accept_13_8_7_3_1_430 60 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 211 (accept_3_3 59 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 211 (Polychromatic418967fa.accept_25_7_22_11_1_12477 57 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 211 (accept_3_3 56 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 211
  (Polychromatic418967fa.accept_17_3_4_7_1_1658 54 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 211 (accept_3_3 53 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 211 (Polychromatic418967fa.accept_19_13_15_2_1_4126 51 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 211 (accept_3_3 50 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 211 (accept_3_3 47 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 211 (accept_3_3 44 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 211
  (Polychromatic418967fa.accept_17_8_4_7_1_7442 42 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 211 (accept_3_3 41 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 211 (accept_3_3 38 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 211 (accept_3_3 35 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 211 (accept_3_3 32 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 211
  (Polychromatic418967fa.accept_13_4_7_3_1_92 30 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 211 (accept_3_3 29 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 211 (accept_3_3 26 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 211 (Polychromatic418967fa.accept_17_8_4_7_1_7442 25 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 211 (accept_3_3 23 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 211 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 211 (accept_3_3 20 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 211
  (Polychromatic418967fa.accept_19_18_15_2_1_11128 18 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 211 (accept_3_3 17 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 72 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 211 (accept_3_3 14 72 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 211
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 211 (accept_3_3 11 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 211 (accept_3_3 8 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 211 (Polychromatic418967fa.accept_22_7_6_13_1_12476 7 72 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 211 (accept_3_3 5 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  211 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 72 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 211 (accept_3_3 2 72 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 72 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 211 (allA_of_3_1 71 71 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 211 (allA_succ_of_accept 69 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 211 (accept_3_3 68 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 211 (Polychromatic418967fa.accept_13_2_5_3_1_406 67 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 211 (accept_3_3 65 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 211 (accept_3_3 62 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 211 (accept_3_3 59 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 211 (Polychromatic418967fa.accept_13_6_5_3_1_426 58 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 211 (accept_3_3 56 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 211 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 211 (accept_3_3 53 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 211 (accept_3_3 50 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 211 (accept_3_3 47 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 211 (accept_3_3 44 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 211 (accept_3_3 41 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 211 (accept_3_3 38 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 211 (accept_3_3 35 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 211 (Polychromatic418967fa.accept_13_8_5_3_1_427 34 70 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 211 (accept_3_3 32 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 211 (accept_3_3 29 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 211 (accept_3_3 26 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 211 (accept_3_3 23 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 211 (accept_3_3 20 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 211 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 211 (accept_3_3 17 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 211 (accept_3_3 14 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 211 (accept_3_3 11 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 211 (accept_3_3 8 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 211 (accept_3_3 5 70 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 211 (accept_3_3 2 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 211
  (allA_succ_of_accept 68 69 211 (accept_3_3 68 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 211 (accept_3_3 65 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 211 (accept_3_3 62 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 211 (Polychromatic418967fa.accept_19_3_12_2_1_9788 60 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 211 (accept_3_3 59 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 211 (accept_3_3 56 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 211 (accept_3_3 53 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 211 (accept_3_3 50 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 211 (Polychromatic418967fa.accept_14_7_13_1_1_922 49 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 211 (accept_3_3 47 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 211 (accept_3_3 44 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 211 (accept_3_3 41 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 211 (accept_3_3 38 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 211 (accept_3_3 35 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 211 (accept_3_3 32 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 211 (Polychromatic418967fa.accept_25_6_19_11_1_6969 31 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 211 (accept_3_3 29 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 211 (accept_3_3 26 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 211 (Polychromatic418967fa.accept_16_8_5_3_1_4297 24 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 211 (accept_3_3 23 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 211 (accept_3_3 20 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 211 (accept_3_3 17 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 211 (accept_3_3 14 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 211 (Polychromatic418967fa.accept_26_13_17_3_1_12475 13 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 211 (accept_3_3 11 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 211 (accept_3_3 8 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 211 (accept_3_3 5 69 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 211 (accept_3_3 2 69 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 211 (allA_of_3_1 68 68 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 211 (allA_succ_of_accept 66 67 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 211 (accept_3_3 65 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 211 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 211 (accept_3_3 62 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 211
  (Polychromatic418967fa.accept_14_4_11_1_1_940 60 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 211 (accept_3_3 59 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 211 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 211 (accept_3_3 56 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 211 (accept_3_3 53 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 211 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 211 (accept_3_3 50 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 211 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 67
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 211
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 211 (accept_3_3 47 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 211 (accept_3_3 44 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 211
  (Polychromatic418967fa.accept_17_8_16_7_1_8792 42 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 211 (accept_3_3 41 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 211 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 211 (accept_3_3 38 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 211 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 211
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 211 (accept_3_3 35 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 211 (accept_3_3 32 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 211
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 30 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 211 (accept_3_3 29 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 211 (Polychromatic418967fa.accept_21_7_4_1_1_3300 28 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 211 (accept_3_3 26 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 211 (accept_3_3 23 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 211 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 211 (accept_3_3 20 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 211
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 211 (accept_3_3 17 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 211 (Polychromatic418967fa.accept_23_15_21_4_1_12474 15 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 211 (accept_3_3 14 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 211 (Polychromatic418967fa.accept_19_13_10_2_1_12473 13 67
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 211 (accept_3_3 11 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 211 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 211 (accept_3_3 8 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 211 (Polychromatic418967fa.accept_21_7_4_1_1_3300 7 67 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 211
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 211 (accept_3_3 5 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  211 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 67 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 211 (accept_3_3 2 67 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 67 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 211 (allA_succ_of_accept 65 66
  211 (accept_3_3 65 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 211 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 66 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 211 (accept_3_3 62 66 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 211 (accept_3_3 59 66
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 211 (Polychromatic418967fa.accept_7_2_3_1_1_10
  58 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 211 (accept_3_3 56 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 211 (accept_3_3 53 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 211 (accept_3_3 50 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 211 (accept_3_3 47 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 211 (accept_3_3 44 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 211 (accept_3_3 41 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 211 (accept_3_3 38 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 211 (Polychromatic418967fa.accept_17_2_15_7_1_6213 36 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 211 (accept_3_3 35 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 211 (accept_3_3 32 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 211 (accept_3_3 29 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 211
  (Polychromatic418967fa.accept_10_7_6_1_1_486 27 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 211 (accept_3_3 26 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 211 (accept_3_3 23 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 211 (accept_3_3 20 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 211 (accept_3_3 17 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 211 (accept_3_3 14 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 211 (accept_3_3 11 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 211 (accept_3_3 8 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 211 (accept_3_3 5 66 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3
  66 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 211 (accept_3_3 2 66 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 211 (allA_of_3_1 65 65 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 211 (allA_succ_of_accept 63 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 211 (accept_3_3 62 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 211 (accept_3_3 59 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 211 (accept_3_3 56 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 211 (accept_3_3 53 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 211 (accept_3_3 50 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621 49 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 211 (accept_3_3 47 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 211 (accept_3_3 44 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 211 (accept_3_3 41 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 211 (accept_3_3 38 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 211 (Polychromatic418967fa.accept_17_2_13_7_1_5011 36 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 211 (accept_3_3 35 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 64 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 211 (accept_3_3 32 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 211 (Polychromatic418967fa.accept_23_8_18_4_1_12472 31 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 211 (accept_3_3 29 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 211 (accept_3_3 26 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 211 (accept_3_3 23 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 211 (accept_3_3 20 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 211 (Polychromatic418967fa.accept_17_2_13_7_1_5011 19 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 211 (accept_3_3 17 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 211 (accept_3_3 14 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 211 (Polychromatic418967fa.accept_19_13_7_2_1_5413 13 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 211 (accept_3_3 11 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 64 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 211 (accept_3_3 8 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 211 (accept_3_3 5 64 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 64 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 211 (accept_3_3 2 64 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 211 (Polychromatic418967fa.accept_18_1_10_13_1_500
  1 64 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 211 (allA_succ_of_accept 62 63 211
  (accept_3_3 62 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 211
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 211 (accept_3_3 59 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  57 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 211 (accept_3_3 56
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 211
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 211 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 211 (accept_3_3 53 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678
  51 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 211 (accept_3_3 50
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 211
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 211 (accept_3_3 47 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 211 (accept_3_3 44
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 211
  (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 211 (accept_3_3 41 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 211 (Polychromatic418967fa.accept_16_7_15_3_1_1302
  39 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 211 (accept_3_3 38
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 211
  (Polychromatic418967fa.accept_17_3_12_7_1_4949 37 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 211 (accept_3_3 35 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  33 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 211 (accept_3_3 32
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 211
  (Polychromatic418967fa.accept_13_5_11_3_1_902 31 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 63 211 (Polychromatic418967fa.accept_20_10_3_11_1_8108 30 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 211 (accept_3_3 29 63 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 211 (Polychromatic418967fa.accept_11_5_8_2_1_588
  27 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 211 (accept_3_3 26
  63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 211
  (Polychromatic418967fa.accept_27_25_9_22_1_12471 25 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 211 (Polychromatic418967fa.accept_18_6_9_13_1_3320 24 63 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 211 (accept_3_3 23 63 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 211 (accept_3_3 20 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 211 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 211 (accept_3_3 17 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 211
  (Polychromatic418967fa.accept_13_2_11_3_1_873 15 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 211 (accept_3_3 14 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 211 (accept_3_3 11 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 211 (accept_3_3 8 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  211 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 211 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 211 (accept_3_3 5 63 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 211
  (Polychromatic418967fa.accept_17_3_12_7_1_4949 3 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 211 (accept_3_3 2 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  211 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 63 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 211
  (allA_of_3_1 62 62 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 211 (allA_succ_of_accept 60 61 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 211 (accept_3_3 59 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 211 (accept_3_3 56 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 211 (accept_3_3 53 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 211 (accept_3_3 50 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 211 (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 211 (accept_3_3 47 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 211 (accept_3_3 44 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 211 (Polychromatic418967fa.accept_19_5_4_2_1_6840 43 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 211 (accept_3_3 41 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 211 (Polychromatic418967fa.accept_16_8_13_3_1_4253 40 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 211 (accept_3_3 38 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 211
  (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 211 (accept_3_3 35 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 211 (accept_3_3 32 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 211 (accept_3_3 29 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 211 (accept_3_3 26 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 211 (accept_3_3 23 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 211 (accept_3_3 20 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 211 (accept_3_3 17 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 211 (Polychromatic418967fa.accept_17_16_10_7_1_2671 16 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 211 (accept_3_3 14 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 211 (accept_3_3 11 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 211 (Polychromatic418967fa.accept_19_9_4_2_1_9753 9 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 211 (accept_3_3 8 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 61 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 211 (accept_3_3 5 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 211 (accept_3_3 2 61 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 211 (allA_succ_of_accept 59 60 211 (accept_3_3 59 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 211 (Polychromatic418967fa.accept_16_10_12_3_1_4252 58 60 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 211 (accept_3_3 56 60 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55
  60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 211 (accept_3_3 53 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 211 (Polychromatic418967fa.accept_21_9_18_1_1_9424 51 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 211 (accept_3_3 50 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 211 (Polychromatic418967fa.accept_17_15_9_7_1_3816 49 60
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 211 (accept_3_3 47 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 211 (accept_3_3 44 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 211
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 211 (accept_3_3 41 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 211 (accept_3_3 38 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 211
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 211 (accept_3_3 35 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 211 (accept_3_3 32 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 211 (accept_3_3 29 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 211 (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 211 (accept_3_3 26 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 211 (accept_3_3 23 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 211 (accept_3_3 20 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 211
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 211 (accept_3_3 17 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 211 (accept_3_3 14 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 211 (Polychromatic418967fa.accept_23_13_14_4_1_12470 13 60 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 211 (accept_3_3 11 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 211 (accept_3_3 8 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 211
  (Polychromatic418967fa.accept_19_6_3_2_1_4119 6 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 211 (accept_3_3 5 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  211 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 60 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 211 (accept_3_3 2 60 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 211 (allA_of_3_1 59 59 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 211 (allA_succ_of_accept 57 58 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 211 (accept_3_3 56 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 211 (Polychromatic418967fa.accept_23_8_12_4_1_12469 54 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 211 (accept_3_3 53 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 211 (accept_3_3 50 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 211 (accept_3_3 47 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 46 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 211 (accept_3_3 44 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 211 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 211 (accept_3_3 41 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 211 (accept_3_3 38 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 211 (accept_3_3 35 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 211 (accept_3_3 32 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 211 (Polychromatic418967fa.accept_25_5_8_11_1_12468 30 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 211 (accept_3_3 29 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 211 (accept_3_3 26 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 211 (accept_3_3 23 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 211 (accept_3_3 20 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 211 (accept_3_3 17 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 211 (accept_3_3 14 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 211 (accept_3_3 11 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 211 (accept_3_3 8 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  211 (Polychromatic418967fa.accept_16_7_10_3_1_2210 7 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 58 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 211 (accept_3_3 5 58 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 211 (accept_3_3 2 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 211 (allA_succ_of_accept 56
  57 211 (accept_3_3 56 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 211 (accept_3_3 53 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 211 (accept_3_3 50 57
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 211
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 211 (accept_3_3 47 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 211 (Polychromatic418967fa.accept_13_6_5_3_1_426
  45 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 211 (accept_3_3 44
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 211 (accept_3_3 41 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 211 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 211 (accept_3_3 38
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 211 (accept_3_3 35 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 211 (accept_3_3 32 57
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 211
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 31 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 211 (accept_3_3 29 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 211 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 211 (accept_3_3 26
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 211 (accept_3_3 23 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 211 (Polychromatic418967fa.accept_13_8_5_3_1_427
  21 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 211 (accept_3_3 20
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 211 (accept_3_3 17 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 211 (accept_3_3 14 57
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 211
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 211 (Polychromatic418967fa.accept_16_12_9_3_1_5363 12 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 211 (accept_3_3 11 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 9
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 211 (accept_3_3 8 57 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 211 (accept_3_3 5 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 211 (accept_3_3 2 57 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 211 (allA_of_3_1 56 56 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 211
  (allA_succ_of_accept 54 55 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 211 (accept_3_3 53 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 211 (accept_3_3 50 55
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 211 (accept_3_3 47 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 46 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 211 (Polychromatic418967fa.accept_19_7_17_2_1_6855
  45 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 211 (accept_3_3 44
  55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 211
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 211 (accept_3_3 41 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 39
  55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 211 (accept_3_3 38 55
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 211 (Polychromatic418967fa.accept_7_2_6_1_1_73
  37 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 211 (accept_3_3 35 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 211 (accept_3_3 32 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 211 (Polychromatic418967fa.accept_16_15_7_3_1_4273 31 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 211 (accept_3_3 29 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 211 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 211 (accept_3_3 26 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 55 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 211 (accept_3_3 23 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 211 (accept_3_3 20 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 211
  (Polychromatic418967fa.accept_23_18_9_4_1_12467 18 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 211 (accept_3_3 17 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 211 (accept_3_3 14 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 211 (accept_3_3 11 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 211 (Polychromatic418967fa.accept_16_10_7_3_1_6601 10 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 211 (accept_3_3 8 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 211 (accept_3_3 5 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  211 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 55 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 211 (accept_3_3 2 55 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 211 (Polychromatic418967fa.accept_24_1_7_19_1_917 1 55 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 211 (allA_succ_of_accept 53 54 211 (accept_3_3 53 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 211 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 54
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 211 (accept_3_3 50 54 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 211 (accept_3_3 47 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 211 (accept_3_3 44 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 211 (Polychromatic418967fa.accept_16_11_6_3_1_6564 43 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 211
  (Polychromatic418967fa.accept_19_4_16_2_1_6967 42 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 211 (accept_3_3 41 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 211 (accept_3_3 38 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 211
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 211 (accept_3_3 35 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 211 (accept_3_3 32 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 211
  (Polychromatic418967fa.accept_19_11_16_2_1_9759 30 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 211 (accept_3_3 29 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 211 (Polychromatic418967fa.accept_21_7_12_1_1_952 28 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 211 (accept_3_3 26 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 211 (accept_3_3 23 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 211 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 211 (accept_3_3 20 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 211 (Polychromatic418967fa.accept_21_19_12_1_1_11027 19 54 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 211 (accept_3_3 17 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 211 (Polychromatic418967fa.accept_17_16_3_7_1_5028 16 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 211 (accept_3_3 14 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 211
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 211 (accept_3_3 11 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 211 (accept_3_3 8 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 54 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 211 (accept_3_3 5 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 211 (accept_3_3 2 54 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 211))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 211 (allA_of_3_1 53 53 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 211
  (allA_succ_of_accept 51 52 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 211 (accept_3_3 50 52 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48
  52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 211 (accept_3_3 47 52
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 211 (Polychromatic418967fa.accept_7_4_3_1_1_87
  46 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 211 (accept_3_3 44 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 211 (accept_3_3 41 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 211 (accept_3_3 38 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 211 (accept_3_3 35 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 211 (accept_3_3 32 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 211 (accept_3_3 29 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 211 (accept_3_3 26 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 211 (accept_3_3 23 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 211 (accept_3_3 20 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 211 (accept_3_3 17 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 211 (accept_3_3 14 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 211 (accept_3_3 11 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 211 (accept_3_3 8 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 211 (accept_3_3 5 52 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 211 (accept_3_3 2 52 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  211)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 211 (allA_succ_of_accept 50 51 211 (accept_3_3
  50 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 211
  (Polychromatic418967fa.accept_19_11_13_2_1_9770 49 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 211 (accept_3_3 47 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 45
  51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 211 (accept_3_3 44 51
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 211
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 211 (accept_3_3 41 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 211 (accept_3_3 38 51
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 211 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 211
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 211 (accept_3_3 35 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 211 (accept_3_3 32 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 211 (accept_3_3 29 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 211 (accept_3_3 26 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 211 (accept_3_3 23 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 211 (accept_3_3 20 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 211 (accept_3_3 17 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 211 (accept_3_3 14 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 211 (accept_3_3 11 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 211 (accept_3_3 8 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 211 (accept_3_3 5 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 211 (accept_3_3 2 51 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 211)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 211 (allA_of_3_1 50 50 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 211
  (allA_succ_of_accept 48 49 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 49 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 211 (accept_3_3 47 49 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 211 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 211 (accept_3_3 44
  49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 211
  (Polychromatic418967fa.accept_17_9_15_7_1_6212 43 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 211 (accept_3_3 41 49 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 211 (Polychromatic418967fa.accept_21_19_7_1_1_3329 40 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 211
  (Polychromatic418967fa.accept_17_5_15_7_1_4992 39 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 211 (accept_3_3 38 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 211 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 211 (accept_3_3 35 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 211
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 211 (accept_3_3 32 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 211 (Polychromatic418967fa.accept_21_10_7_1_1_9464 31 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 211 (accept_3_3 29 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 211
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 211 (accept_3_3 26 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 211 (accept_3_3 23 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 211
  (Polychromatic418967fa.accept_25_21_24_11_1_12466 21 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 49 211 (accept_3_3 20 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 49 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 211 (accept_3_3 17 49 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 211
  (Polychromatic418967fa.accept_19_16_11_2_1_12465 16 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 211 (accept_3_3 14 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 211
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 211 (accept_3_3 11 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 211 (Polychromatic418967fa.accept_17_9_15_7_1_6212 9 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 211 (accept_3_3 8 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 211 (accept_3_3 5 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  211 (Polychromatic418967fa.accept_16_4_1_3_1_6581 4 49 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 211 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 211 (accept_3_3 2 49 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 211 (Polychromatic418967fa.accept_23_1_3_4_1_7340 1 49 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 211)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 211 (allA_succ_of_accept 47 48 211 (accept_3_3 47 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 48 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 211 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 48 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 211 (accept_3_3 44 48 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 211 (accept_3_3 41 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 211 (accept_3_3 38 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 211 (accept_3_3 35 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 211 (accept_3_3 32 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 211 (accept_3_3 29 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 211 (Polychromatic418967fa.accept_17_10_14_7_1_2679 27 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 211 (accept_3_3 26 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 211 (accept_3_3 23 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 211 (Polychromatic418967fa.accept_25_22_23_11_1_12464 22 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 211 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 211 (accept_3_3 20 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 211
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 211 (accept_3_3 17 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 211 (accept_3_3 14 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 211 (accept_3_3 11 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 211 (accept_3_3 8 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 211 (accept_3_3 5 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  211 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 48 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 211 (accept_3_3 2 48 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 211)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 211 (allA_of_3_1 47 47 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 211 (allA_succ_of_accept 45 46
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 211 (accept_3_3 44 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 211 (accept_3_3 41 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 211 (accept_3_3 38 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 211 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 211 (accept_3_3 35 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 46 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 211 (accept_3_3 32 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 211 (accept_3_3 29 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 211 (accept_3_3 26 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 211 (accept_3_3 23 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 211 (accept_3_3 20 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 211 (Polychromatic418967fa.accept_21_18_4_1_1_12463 18 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 211 (accept_3_3 17 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 211 (accept_3_3 14 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 211 (accept_3_3 11 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 211 (accept_3_3 8 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 46 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 211 (accept_3_3 5 46 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 211 (accept_3_3 2 46 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  211)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 211 (allA_succ_of_accept 44 45 211 (accept_3_3 44 45
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 211
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 211 (accept_3_3 41 45 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 211 (accept_3_3 38 45
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 211 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 211
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 211 (accept_3_3 35 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 211 (accept_3_3 32 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 31 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 211 (accept_3_3 29 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 211 (accept_3_3 26 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 211 (accept_3_3 23 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 211 (accept_3_3 20 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 211 (accept_3_3 17 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 211 (accept_3_3 14 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 211 (Polychromatic418967fa.accept_17_13_11_7_1_4961 13 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 211 (accept_3_3 11 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 211 (accept_3_3 8 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 211 (Polychromatic418967fa.accept_21_7_3_1_1_3321 7 45 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 211 (accept_3_3 5 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 45 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 211 (accept_3_3 2 45 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 45 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 211))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  211 (allA_of_3_1 44 44 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 211 (allA_succ_of_accept 42 43 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 211 (accept_3_3 41 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 40 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 211 (accept_3_3 38 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 211
  (Polychromatic418967fa.accept_17_2_9_7_1_5002 36 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 211 (accept_3_3 35 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 211 (accept_3_3 32 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 211 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 211 (accept_3_3 29 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 211 (accept_3_3 26 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 211 (accept_3_3 23 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 211 (accept_3_3 20 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 211
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 211 (accept_3_3 17 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 211 (Polychromatic418967fa.accept_19_16_5_2_1_8375 16 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 211 (accept_3_3 14 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 211 (Polychromatic418967fa.accept_20_13_3_11_1_9586 13 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 211 (accept_3_3 11 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 211 (Polychromatic418967fa.accept_22_9_21_13_1_10830 9 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 211 (accept_3_3 8 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 211 (accept_3_3 5 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  211 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 43 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 211 (accept_3_3 2 43 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 211)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 211 (allA_succ_of_accept 41 42 211 (accept_3_3 41 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 42 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 211 (accept_3_3 38 42 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 211 (accept_3_3 35 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 211 (accept_3_3 32 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 211 (Polychromatic418967fa.accept_17_14_8_7_1_6183 31 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 211 (accept_3_3 29 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 211 (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 211 (accept_3_3 26 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 211
  (Polychromatic418967fa.accept_19_5_4_2_1_6840 24 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 211 (accept_3_3 23 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 211 (Polychromatic418967fa.accept_23_22_19_4_1_12462 22 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 211 (accept_3_3 20 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 211
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 211 (accept_3_3 17 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 211 (accept_3_3 14 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 211 (accept_3_3 11 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 211 (accept_3_3 8 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 211 (accept_3_3 5 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 42 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 211 (accept_3_3 2 42 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 211)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 211
  (allA_of_3_1 41 41 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 211 (allA_succ_of_accept 39 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 211 (accept_3_3 38 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 211 (Polychromatic418967fa.accept_13_11_1_3_1_910 37 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 211 (accept_3_3 35 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 211 (accept_3_3 32 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 211 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 211 (accept_3_3 29 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 211 (accept_3_3 26 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 211 (accept_3_3 23 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 211 (accept_3_3 20 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 211 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 211 (accept_3_3 17 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 211 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 211 (accept_3_3 14 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 211 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 211 (accept_3_3 11 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 211 (accept_3_3 8 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 211 (accept_3_3 5 40 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 211 (accept_3_3 2 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  211 (Polychromatic418967fa.accept_22_1_18_13_1_10865 1 40 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 40 211)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 211 (allA_succ_of_accept 38 39 211
  (accept_3_3 38 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 211 (accept_3_3 35 39 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 211 (accept_3_3 32 39
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 211 (Polychromatic418967fa.accept_7_3_4_1_1_71
  31 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 211
  (Polychromatic418967fa.accept_18_12_3_13_1_4494 30 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 211 (accept_3_3 29 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 211 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 39 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 211 (accept_3_3 26 39 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 211 (accept_3_3 23 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 211 (accept_3_3 20 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 211
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 211 (accept_3_3 17 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 211 (accept_3_3 14 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 211 (Polychromatic418967fa.accept_19_13_1_2_1_11154 13 39 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 211 (accept_3_3 11 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 211 (accept_3_3 8 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 211 (accept_3_3 5 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 211 (accept_3_3 2 39 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 211))))))))))))))))))))))))))))))))))))))) (allB_succ 38 211
  (allA_of_3_1 38 38 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 211 (allA_succ_of_accept 36 37 211
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 211 (accept_3_3 35 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 211 (accept_3_3 32 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 211 (accept_3_3 29 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 211 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 211 (accept_3_3 26 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 211 (accept_3_3 23 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 211 (accept_3_3 20 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 211 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 37 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 211 (accept_3_3 17 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 211 (accept_3_3 14 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 211 (accept_3_3 11 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 211 (accept_3_3 8 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 211 (accept_3_3 5 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  211 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 37 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 211 (accept_3_3 2 37 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 37 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 211))))))))))))))))))))))))))))))))))))) (allB_succ 36 211
  (allA_succ_of_accept 35 36 211 (accept_3_3 35 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 211 (accept_3_3 32 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 211
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 211 (accept_3_3 29 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 211 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 211 (accept_3_3 26 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 211
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 211 (accept_3_3 23 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 211 (accept_3_3 20 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 211 (accept_3_3 17 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 211 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 211 (accept_3_3 14 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 211 (Polychromatic418967fa.accept_17_13_2_7_1_6122 13 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 211 (accept_3_3 11 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 211 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 211 (accept_3_3 8 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 211
  (Polychromatic418967fa.accept_13_6_10_3_1_897 6 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 211 (accept_3_3 5 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  211 (Polychromatic418967fa.accept_19_4_17_2_1_5409 4 36 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 211 (accept_3_3 2 36 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 36 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 211)))))))))))))))))))))))))))))))))))) (allB_succ 35
  211 (allA_of_3_1 35 35 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 211 (allA_succ_of_accept 33 34 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 211 (accept_3_3 32 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 211 (accept_3_3 29 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 211 (accept_3_3 26 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 211 (accept_3_3 23 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 34 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 211 (accept_3_3 20 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 211 (accept_3_3 17 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 211 (accept_3_3 14 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 211 (accept_3_3 11 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 211 (accept_3_3 8 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 211 (accept_3_3 5 34 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 34 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 211 (accept_3_3 2 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 211)))))))))))))))))))))))))))))))))) (allB_succ 33 211 (allA_succ_of_accept 32 33 211 (accept_3_3 32 33
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 211 (Polychromatic418967fa.accept_7_3_5_1_1_72
  31 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 211 (accept_3_3 29 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 211 (accept_3_3 26 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 211 (accept_3_3 23 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 211 (accept_3_3 20 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 211 (accept_3_3 17 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 211 (accept_3_3 14 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 211 (accept_3_3 11 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 211 (accept_3_3 8 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 211 (accept_3_3 5 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 211 (accept_3_3 2 33 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 211))))))))))))))))))))))))))))))))) (allB_succ 32 211
  (allA_of_3_1 32 32 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 211 (allA_succ_of_accept 30 31 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 211 (accept_3_3 29 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 211 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 211 (accept_3_3 26 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 211
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 211 (accept_3_3 23 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 211 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 211 (accept_3_3 20 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 211 (accept_3_3 17 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 211 (accept_3_3 14 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 211 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 31 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 211 (accept_3_3 11 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 211 (Polychromatic418967fa.accept_17_10_14_7_1_2679 10 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 211 (accept_3_3 8 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 31 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 211
  (Polychromatic418967fa.accept_13_6_5_3_1_426 6 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 211 (accept_3_3 5 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 211 (Polychromatic418967fa.accept_19_3_12_2_1_9788 3 31 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 211 (accept_3_3 2 31 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 211 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 31 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 211))))))))))))))))))))))))))))))) (allB_succ 30 211
  (allA_succ_of_accept 29 30 211 (accept_3_3 29 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 211 (accept_3_3 26 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 211 (accept_3_3 23 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 211 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 211 (accept_3_3 20 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 211
  (Polychromatic418967fa.accept_21_18_9_1_1_9467 18 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 211 (accept_3_3 17 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 211 (accept_3_3 14 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 211
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 211 (accept_3_3 11 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 211 (accept_3_3 8 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 211 (accept_3_3 5 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  211 (Polychromatic418967fa.accept_19_4_11_2_1_11111 4 30 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 30 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 211 (accept_3_3 2 30 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 211)))))))))))))))))))))))))))))) (allB_succ 29 211
  (allA_of_3_1 29 29 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 211 (allA_succ_of_accept 27 28 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 211 (accept_3_3 26 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 211 (accept_3_3 23 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 211 (accept_3_3 20 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 211 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 211 (accept_3_3 17 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 211 (accept_3_3 14 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 211 (accept_3_3 11 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 211 (accept_3_3 8 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 211 (accept_3_3 5 28 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 28 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 211 (accept_3_3 2 28 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 1
  28 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 211))))))))))))))))))))))))))))
  (allB_succ 27 211 (allA_succ_of_accept 26 27 211 (accept_3_3 26 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 211 (Polychromatic418967fa.accept_19_6_8_2_1_6914 25 27 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 211 (accept_3_3 23 27 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 211 (accept_3_3 20 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 211 (accept_3_3 17 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 211
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 211 (accept_3_3 14 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 211 (accept_3_3 11 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 211 (accept_3_3 8 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 211 (accept_3_3 5 27 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 211
  (Polychromatic418967fa.accept_17_3_10_7_1_2646 3 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 211 (accept_3_3 2 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  211 (Polychromatic418967fa.accept_17_1_10_7_1_12461 1 27 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 211))))))))))))))))))))))))))) (allB_succ 26 211 (allA_of_3_1 26 26 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 211 (allA_succ_of_accept 24 25 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 211 (accept_3_3 23 25 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 211 (accept_3_3 20 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 211 (accept_3_3 17 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 25 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 211 (accept_3_3 14 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 211 (accept_3_3 11 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 211 (accept_3_3 8 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 211 (accept_3_3 5 25 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 25 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 211 (accept_3_3 2 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 211))))))))))))))))))))))))) (allB_succ 24 211 (allA_succ_of_accept 23 24 211 (accept_3_3 23 24 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 211 (Polychromatic418967fa.accept_15_7_9_1_1_473
  22 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 211 (accept_3_3 20 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 211 (accept_3_3 17 24 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 211
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 211 (accept_3_3 14 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 211 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 211 (accept_3_3 11 24 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 211 (accept_3_3 8 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 24 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 211 (accept_3_3 5 24 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  24 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 211 (accept_3_3 2 24 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 211)))))))))))))))))))))))) (allB_succ
  23 211 (allA_of_3_1 23 23 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 211 (allA_succ_of_accept 21 22
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 211 (accept_3_3 20 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 22 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 211 (accept_3_3 17 22 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 22 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 211 (accept_3_3 14 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 211 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 22 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 211 (accept_3_3 11 22 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 22
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 211 (accept_3_3 8 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 22 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 22 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 211 (accept_3_3 5 22 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 211 (accept_3_3 2 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 211)))))))))))))))))))))) (allB_succ 21 211 (allA_succ_of_accept 20 21 211 (accept_3_3 20 21 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 211 (accept_3_3 17 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 211 (accept_3_3 14 21 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 21 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 211
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 211 (accept_3_3 11 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 21 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 211 (accept_3_3 8 21 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 211 (accept_3_3 5 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 211 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 211 (accept_3_3 2 21 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 211))))))))))))))))))))) (allB_succ 20 211 (allA_of_3_1 20 20
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 211 (allA_succ_of_accept 18 19 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 211 (accept_3_3 17 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 211 (accept_3_3 14 19 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 211 (accept_3_3 11 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 19 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 211 (accept_3_3 8 19 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 211 (accept_3_3 5 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 211 (accept_3_3 2 19 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 19 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 211))))))))))))))))))) (allB_succ 18 211 (allA_succ_of_accept 17
  18 211 (accept_3_3 17 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 211
  (Polychromatic418967fa.accept_19_16_18_2_1_6934 16 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 211 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 18 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 211 (accept_3_3 14 18 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12
  18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 211 (accept_3_3 11 18
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 211 (Polychromatic418967fa.accept_7_3_4_1_1_71
  10 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 211 (accept_3_3 8 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18
  211 (Polychromatic418967fa.accept_20_7_18_11_1_5080 7 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 211 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 18 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 211 (accept_3_3 5 18 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 211 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 18 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 211 (accept_3_3 2 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 211)))))))))))))))))) (allB_succ 17 211 (allA_of_3_1 17 17 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 211 (allA_succ_of_accept 15 16 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 211 (accept_3_3 14 16 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 211 (accept_3_3 11 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 211 (accept_3_3 8 16 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 211 (accept_3_3 5 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  211 (Polychromatic418967fa.accept_19_4_16_2_1_6967 4 16 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 16 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 211 (accept_3_3 2 16 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 211)))))))))))))))) (allB_succ 15 211
  (allA_succ_of_accept 14 15 211 (accept_3_3 14 15 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 211 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 15 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 211 (accept_3_3 11 15 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 211 (accept_3_3 8 15 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 15 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 211 (accept_3_3 5 15 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  15 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 211 (accept_3_3 2 15 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 211))))))))))))))) (allB_succ 14 211
  (allA_of_3_1 14 14 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 211 (allA_succ_of_accept 12 13 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 211 (accept_3_3 11 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 211 (accept_3_3 8 13 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 211 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 13 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 211 (accept_3_3 5 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  211 (Polychromatic418967fa.accept_20_4_13_11_1_12460 4 13 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 211 (Polychromatic418967fa.accept_15_3_13_1_1_479 3 13 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 211 (accept_3_3 2 13 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 211 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1 13 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 211))))))))))))) (allB_succ 12 211
  (allA_succ_of_accept 11 12 211 (accept_3_3 11 12 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 211 (accept_3_3 8 12 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 211 (accept_3_3 5 12 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 211 (accept_3_3 2 12 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 211)))))))))))) (allB_succ 11 211 (allA_of_3_1 11 11 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 211 (allA_succ_of_accept 9 10 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 211 (accept_3_3 8 10 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 211 (accept_3_3 5 10 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 211 (accept_3_3 2 10 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 211)))))))))) (allB_succ 9 211
  (allA_succ_of_accept 8 9 211 (accept_3_3 8 9 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 211
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 9 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 211 (accept_3_3 5 9 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 211 (accept_3_3 2 9 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 211 (Polychromatic418967fa.accept_19_1_9_2_1_6945 1
  9 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 211))))))))) (allB_succ 8 211
  (allA_of_3_1 8 8 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 211 (allA_succ_of_accept 6 7 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 211 (accept_3_3 5 7 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 211 (accept_3_3 2 7 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 211))))))) (allB_succ 6 211 (allA_succ_of_accept 5 6 211
  (accept_3_3 5 6 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 211
  (Polychromatic418967fa.accept_11_4_6_2_1_51 4 6 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 211 (accept_3_3 2 6 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 211)))))) (allB_succ 5 211 (allA_of_3_1 5 5 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 211 (allA_succ_of_accept 3 4 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 211 (accept_3_3 2 4 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 211
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 4 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 211)))) (allB_succ 3 211 (allA_succ_of_accept 2 3 211 (accept_3_3 2 3 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 211))) (allB_succ 2 211 (allA_of_3_1 2 2 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


