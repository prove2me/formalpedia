-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch255_Segment001
-- name    : Polychromatic418967fa_Branch255_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:25.11942+00:00
-- url     : https://prove2.me/theorems/9469011f-9f9f-4bdd-9d08-ed7847a6044c
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch255_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_255_segment_001 : allB 142 255 :=
  allB_succ' 115 141 255 (Eq.refl Bool.true) (allA_succ_of_gcd 114 141 255 3 38 47 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 141 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 113 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 112 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 141 255 3 37 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27
  110 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 109 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 141 255 3 36 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 141 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 141 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 141 255 3 35 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 141 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  103 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 141 255 3 34 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 101 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 141 255 3 33 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 98
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 97 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 141 255 3 32 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 141 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 141 255 3 31 47 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 92 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 141 255 3 30 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 89
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 88 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 141 255 3 29 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  85 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 141 255 3 28 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 141 255 3 27 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 141 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 141 255 3 26 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 141 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  76 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 141 255 3 25 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 141 255 3 24 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 141 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 141 255 3 23 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  67 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 141 255 3 22 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 141 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 141 255 3 21 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 255 3 20 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 141 255 3 19 47 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 255 3 18 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 255 3 17 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  49 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 255 3 16 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 255 3 15 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 255 3 14 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 255 3 13 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 255 3 12 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 255 3 11 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 141 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 255 3 10 47 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 255 3 9 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 255 3 8 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 255 3 7 47 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 255 3 6 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 255 3 5 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 255 3 4 47 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 255 3 3 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 255 3 2 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 255 3 1 47 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 140 255 (Eq.refl Bool.true) (allA_succ_of_gcd 115 140 255 5 23 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 140 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 114 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 113 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 140 255 (accept_3_4 112 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 140 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 111 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 140 255 5 22 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 140 255 (accept_3_4 109 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 140 255
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 108 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 107 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 140 255 (accept_3_4 106 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 140 255 5 21 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 140 255 (Polychromatic418967fa.accept_11_5_8_2_1_588
  104 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 140 255 (accept_3_4
  103 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 140 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 102 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 101 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 255 5 20 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 99
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 140 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 98 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 140 255 (accept_3_4 97 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 140 255 5 19 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 140 255 (accept_3_4 94 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 140 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 93 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 140 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 140 255 (accept_3_4 91 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 140 255 5 18 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 140 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 140 255 (accept_3_4 88 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 140 255 (Polychromatic418967fa.accept_21_2_14_3_1_4933 86 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 140 255 5 17 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 140 255
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 84 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 140 255 (accept_3_4 82 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 140 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 81 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 140 255 5 16 28 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 140 255 (accept_3_4 79
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 140 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 78 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 140 255 (accept_3_4 76 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 140 255 5 15 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 140 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 140 255 (accept_3_4 73 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 140 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 140
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 140 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 140 255 5 14 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 255
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 68 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 140 255 (accept_3_4 67 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 140 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 140 255 5 13 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 140 255 (accept_3_4 64 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 255 (accept_3_4 61 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  140 255 5 12 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 255 (accept_3_4 58 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 140 255 (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 140 255 5 11 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 140 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 255 (accept_3_4 52
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 255 5 10 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 255 (accept_3_4 49 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 140 255 (Polychromatic418967fa.accept_18_12_14_3_1_2655 48 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 255 (accept_3_4 46
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 140 255 5 9 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 140 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 255 (accept_3_4 43 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 255 5 8 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 255
  (Polychromatic418967fa.accept_19_1_7_8_1_3262 39 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 140 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 255 (accept_3_4 37 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 140 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 140 255 5 7 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 140 255 (accept_3_4 34 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205
  33 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 255
  (Polychromatic418967fa.accept_21_11_14_3_1_11142 32 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 140 255 (accept_3_4 31 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 255 5 6 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 255 (accept_3_4 28 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 140 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 255 (Polychromatic418967fa.accept_9_8_5_3_1_777
  26 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 140 255 5 5 28 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 140 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 24 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 255 (accept_3_4 22 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 140 255 (Polychromatic418967fa.accept_22_21_8_13_1_15587 21 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 255 5 4 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 255 (accept_3_4 19 140 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 255 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 255 (accept_3_4 16 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  140 255 5 3 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 140 255 (Polychromatic418967fa.accept_19_14_7_8_1_10053 14 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 140 255 (accept_3_4 13 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 140 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 255 5 2 28 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 255
  (Polychromatic418967fa.accept_18_9_14_3_1_6407 9 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 255 (accept_3_4 7 140 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 140 255 5 1 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 140 255 (accept_3_4 4 140 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 140 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 255 (accept_3_4 1 140 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 139 255 (Eq.refl Bool.true) (allA_succ_of_accept 116 139 255 (accept_3_5 116 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 139 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 115 139
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 139 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 114 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 139 255 (accept_3_5 113 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 139 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 111 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 139 255 (accept_3_5 110 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 139 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 139
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 139 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 108 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 139 255 (accept_3_5 107 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 139 255 (accept_3_5 104 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 139 255 (Polychromatic418967fa.accept_13_12_9_8_1_2595 103
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 139 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 102 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 139 255 (accept_3_5 101 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 139 255 (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 139 255 (accept_3_5 98 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 139 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 97 139 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 139 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 96 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 139 255 (accept_3_5 95 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 139 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 139 255 (accept_3_5 92 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 139 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 139 255
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 90 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 139 255 (accept_3_5 89 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 139 255 (accept_3_5 86 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 139 255 (Polychromatic418967fa.accept_13_7_9_8_1_188 85 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 139 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 139 255 (accept_3_5 83 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 139 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 255 (accept_3_5 80 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 139 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 255 (accept_3_5 77 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 255 (accept_3_5 74 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 139 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 255 (accept_3_5 71 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 255 (accept_3_5 68 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 255
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 66 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 255 (accept_3_5 65 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 255 (accept_3_5 62 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 139 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 255 (accept_3_5 59 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 255 (accept_3_5 56 139 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 139 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 255
  (Polychromatic418967fa.accept_10_4_9_5_1_84 54 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 255 (accept_3_5 53 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 255 (accept_3_5 50 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 49 139 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 255
  (Polychromatic418967fa.accept_18_12_13_3_1_6427 48 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 139 255 (accept_3_5 47 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 139
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 255 (accept_3_5 44 139
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 255 (accept_3_5 41 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 255 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 255 (accept_3_5 38
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 139 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 255 (accept_3_5 35 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203
  33 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 255 (accept_3_5 32
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 139 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 255 (accept_3_5 29 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 255 (Polychromatic418967fa.accept_13_1_9_8_1_1734
  27 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 255 (accept_3_5 26
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 255 (accept_3_5 23 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 255 (Polychromatic418967fa.accept_10_1_9_5_1_83
  21 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 255 (accept_3_5 20
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 139 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 255 (accept_3_5 17 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203
  15 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 255 (accept_3_5 14
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 255
  (Polychromatic418967fa.accept_19_13_6_8_1_8741 13 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 139 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 255 (accept_3_5 11 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 255 (accept_3_5 8 139
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 139 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 255 (accept_3_5 5 139 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 139 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202
  3 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 255 (accept_3_5 2
  139 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 139 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 139
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 138 255 (Eq.refl Bool.true) (allA_succ_of_gcd 117 138 255 3 39 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 138 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 116 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 138 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 115 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 138 255 3 38 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 138 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 112 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 138 255 3 37 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 138 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  110 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 255 3 36 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 107 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 138 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  106 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 138 255 3 35 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 138 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 104 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 138 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 103 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 138 255 3 34 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 138 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 100 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 138 255 3 33 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 138 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 98 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 138 255 3 32 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 138 255
  (Polychromatic418967fa.accept_21_11_12_3_1_6461 95 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 138 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 94 138 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 138 255 3 31 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 138 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 92 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 138 255 (Polychromatic418967fa.accept_16_11_10_15_1_6301 91 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 138 255 3 30 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 138 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 138 255 3 29 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 86
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 85 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 255 3 28 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 83 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  82 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 138 255 3 27 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 138 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 138 255 3 26 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 76 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 138 255 3 25 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 138 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 74 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 138 255 3 24 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 138 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 138 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 138 255 3 23 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 138 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  68 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 255 3 22 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  64 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 138 255 3 21 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 138 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 138 255 3 20 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 138 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 59
  138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 138 255 3 19 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 138 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 255
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 55 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 255 3 18 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  52 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 138 255 3 17 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 138 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 255 3 16 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008
  47 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 138 255 3 15 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 255 3 14 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 138 255 3 13 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 138 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 255 3 12 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 255 (Polychromatic418967fa.accept_19_16_5_8_1_3253 35 138 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 138 255 3 11 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 138 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 138 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 255
  (Polychromatic418967fa.accept_18_13_12_3_1_3857 31 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 138 255 3 10 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 138 255 3 9 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 138 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 255 3 8 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 255 3 7 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 255
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 255 3 6 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 255 3 5 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 255 3 4 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 255
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 138 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 138 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 255 3 3 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 255 3 2 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 255
  (Polychromatic418967fa.accept_11_4_6_2_1_51 4 138 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 138 255 3 1 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 138 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 138 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 137 255 (Eq.refl Bool.true) (allA_succ_of_accept 118 137 255 (accept_3_4 118 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 137 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 117 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 137 255 (accept_3_4 115 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 113 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 137 255 (accept_3_4 112 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 111 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 137 255 (accept_3_4 109 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 137 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 108 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 137 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 137 255 (accept_3_4 106 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 105 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 137 255 (accept_3_4 103 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 137 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 101 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 137 255 (accept_3_4 100 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 137 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 137 255 (accept_3_4 97 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 137 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 95 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 255 (accept_3_4 94 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 137 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 137 255 (accept_3_4 91 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 137 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 255 (accept_3_4 88 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 255 (accept_3_4 85 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 255 (Polychromatic418967fa.accept_22_18_5_13_1_10842 84 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 255 (accept_3_4 82 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 255 (accept_3_4 79 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 255 (accept_3_4 76 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 75 137 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 255 (accept_3_4 73 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 255 (accept_3_4 70 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 255 (accept_3_4 67 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 255 (Polychromatic418967fa.accept_20_5_17_15_1_6858 65 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 255 (accept_3_4 64 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 255 (accept_3_4 61 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 255 (accept_3_4 58 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 255 (accept_3_4 55 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 255 (accept_3_4 52 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 255 (accept_3_4 49 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 255 (Polychromatic418967fa.accept_19_9_4_8_1_8805 47 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 255 (accept_3_4 46 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 137
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 255 (accept_3_4 43 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 255 (accept_3_4 40 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 255 (Polychromatic418967fa.accept_20_19_17_15_1_2690 39 137 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 255 (accept_3_4 37 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 255 (accept_3_4 34 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 255 (accept_3_4 31 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 255 (accept_3_4 28 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 255 (accept_3_4 25 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 255 (accept_3_4 22 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 255 (accept_3_4 19 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 255 (accept_3_4 16 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 255 (accept_3_4 13 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 255 (Polychromatic418967fa.accept_22_11_5_13_1_10845 11 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 255 (accept_3_4 10 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 137 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 255 (accept_3_4 7 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 255 (accept_3_4 4 137 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 137 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 255 (accept_3_4 1 137 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 136 255 (Eq.refl Bool.true) (allA_succ_of_gcd 119 136 255 17 7 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 136 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 118 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 136 255 (Polychromatic418967fa.accept_21_12_10_3_1_11112 117 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 136 255 (accept_3_5 116 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 136 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 114 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 136 255 (accept_3_5 113 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 112 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 136 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 111 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 136 255 (accept_3_5 110 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 109 136
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 136 255
  (Polychromatic418967fa.accept_11_9_4_2_1_600 108 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 136 255 (accept_3_5 107 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 136 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 105 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 136 255 (accept_3_5 104 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 136
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 136 255 17 6 8 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 136 255 (accept_3_5
  101 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 136 255
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 100 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 136 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 99 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 136 255 (accept_3_5 98 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 136 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 96 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 136 255 (accept_3_5 95 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 136 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092 93 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 136 255 (accept_3_5 92 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 136 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 90 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 136 255 (accept_3_5 89 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 136 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 136 255 (accept_3_5 86 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 136 255 17 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 136 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 136 255 (accept_3_5 83 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 136 255 (Polychromatic418967fa.accept_19_6_3_8_1_7283
  82 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 136 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 81 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 136 255 (accept_3_5 80 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 136 255 (accept_3_5 77 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 136 255
  (Polychromatic418967fa.accept_11_9_4_2_1_600 75 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 136 255 (accept_3_5 74 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 136 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 136 255 (accept_3_5 71 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 136 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 136 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 136 255 17 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 136
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 136 255 (accept_3_5 65 136
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 136 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 64 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 136 255 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 255 (accept_3_5 62 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191
  60 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 136 255 (accept_3_5 59
  136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 136 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 58 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 136 255 (Polychromatic418967fa.accept_16_9_8_15_1_5095 57 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 255 (accept_3_5 56 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 255 (Polychromatic418967fa.accept_10_4_6_5_1_74
  54 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 255 (accept_3_5 53
  136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 136 255 17 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 136 255 (accept_3_5 50 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 255 (accept_3_5 47 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 255 (Polychromatic418967fa.accept_22_2_4_13_1_10973 46 136
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 255
  (Polychromatic418967fa.accept_20_5_16_15_1_3957 45 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 136 255 (accept_3_5 44 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 255 (accept_3_5 41 136 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190
  40 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 255 (accept_3_5 38 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 255 (accept_3_5 35 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 255 17 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 255 (accept_3_5 32
  136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 136 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 255 (accept_3_5 29 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 136 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 255 (accept_3_5 26 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 255 (accept_3_5 23 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 21 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 255 (accept_3_5 20 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 136 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 136 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 136 255 17 1 8 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 136 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 255 (accept_3_5 14 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 255
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 136 255 (accept_3_5 11 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 136 255 (Polychromatic418967fa.accept_20_10_16_15_1_1536 10 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  9 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 255 (accept_3_5 8
  136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 136 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 255 (accept_3_5 5 136 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 136 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 136 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 255
  (Polychromatic418967fa.accept_22_3_4_13_1_13947 3 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 255 (accept_3_5 2 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 135 255 (Eq.refl Bool.true) (allA_succ_of_gcd 120 135 255 15 8 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 135 255
  (Polychromatic418967fa.accept_19_5_2_8_1_8803 119 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 118 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 135 255 3 39 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 135 255
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 116 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 115 135 255 5 23 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 114 135 255 3 38 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 113 135
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 135 255
  (Polychromatic418967fa.accept_21_7_9_3_1_8059 112 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 135 255 3 37 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 110 135 255 5 22 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 135 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 109 135 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 135 255 3 36 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 135 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 107 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 135 255 15 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  104 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 103 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 135 255 3 34 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 135 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 101 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 135 255 5 20 27 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 135 255 3 33 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 135 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 98 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 135 255 3 32 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 135 255 5 19 27 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 135 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 94 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 135 255 3 31 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 135 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 91 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 135 255 15 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 255
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 88 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 135 255 3 29 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 255 (Polychromatic418967fa.accept_16_6_7_15_1_1942 86 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 135 255 5 17 27 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 135 255 3 28 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 135 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 135 255 3 27 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 135 255 5 16 27 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 255
  (Polychromatic418967fa.accept_13_1_5_8_1_207 79 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 135 255 3 26 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 135 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 135 255 15 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 135 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 74 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 73 135
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 135 255 3 24 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 135 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 135 255 5 14 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 135 255 3 23 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 135 255 3 22 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 135 255 5 13 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 135 255 3 21 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 135 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 255 15 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 59 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 135 255 (Polychromatic418967fa.accept_19_1_2_8_1_10129 58 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 255 3 19 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 135 255 5 11 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 135 255 3 18 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 135 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 53 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 255
  (Polychromatic418967fa.accept_19_14_2_8_1_5925 52 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 135 255 3 17 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 135 255 5 10 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 135 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 255 3 16 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 255 (Polychromatic418967fa.accept_16_14_7_15_1_3947 46 135 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 255 15 3 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 44 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 255 3 14 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 255 5 8 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 135 255 3 13 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 255
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 37 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 255 3 12 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 135 255 5 7 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 34
  135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 255 3 11 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 32 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 31 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 255 15 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 255
  (Polychromatic418967fa.accept_21_7_9_3_1_8059 28 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 255 3 9 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 255 5 5 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 135 255 3 8 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  23 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 255 3 7 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 135 255 5 4 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 135 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 255 3 6 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 255 (Polychromatic418967fa.accept_21_17_9_3_1_6437
  17 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 255 15 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 255 3 4 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 135 255 5 2 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 135 255 3 3 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 135 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 255
  (Polychromatic418967fa.accept_18_7_9_3_1_800 7 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 255 3 2 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 135 255 5 1 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 135 255 (Polychromatic418967fa.accept_22_4_3_13_1_7770 4 135 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 255 3 1 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 2 135 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 134 255 (Eq.refl Bool.true) (allA_succ_of_accept 121 134 255 (accept_3_4 121 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 134 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 120
  134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 134 255 (accept_3_4 118 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 116 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 134 255 (accept_3_4 115 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 134
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 134 255 (accept_3_4 112 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 134 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 111 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 110 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 134 255 (accept_3_4 109 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 134 255 (Polychromatic418967fa.accept_19_13_1_8_1_3281 108
  134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 134 255 (accept_3_4 106 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 134 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 104 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 134 255 (accept_3_4 103 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 134
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 134 255 (accept_3_4 100 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 134 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 99 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 134 255 (Polychromatic418967fa.accept_21_14_8_3_1_8085 98 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 134 255 (accept_3_4 97 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 134 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 134 255 (accept_3_4 94 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 134 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 134 255 (accept_3_4 91 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 134 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 134 255 (accept_3_4 88 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 86 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 134 255 (accept_3_4 85 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 134 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 84 134 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 134 255 (accept_3_4 82 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 134 255 (Polychromatic418967fa.accept_21_17_8_3_1_9576 80 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 134 255 (accept_3_4 79 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 134 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 134 255 (accept_3_4 76 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 134 255 (accept_3_4 73 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 134 255 (accept_3_4 70 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 134 255 (accept_3_4 67 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 134 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 134 255 (accept_3_4 64 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 134 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 134 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 62 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 134 255 (accept_3_4 61 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 134 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 134 255 (accept_3_4 58 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 134 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 134 255 (accept_3_4 55 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 134 255 (accept_3_4 52 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 134 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 134 255 (accept_3_4 49 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 134 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 134 255 (accept_3_4 46 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 255 (accept_3_4 43 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 255 (accept_3_4 40 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 255 (accept_3_4 37 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 255 (accept_3_4 34 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 255 (accept_3_4 31 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 255 (accept_3_4 28 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 255 (Polychromatic418967fa.accept_18_9_8_3_1_2702 27 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 255 (accept_3_4 25 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 255 (accept_3_4 22 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 255 (accept_3_4 19 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 255 (accept_3_4 16 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 255 (accept_3_4 13 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 255 (accept_3_4 10 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 255 (Polychromatic418967fa.accept_20_8_14_15_1_6932 8 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 255 (accept_3_4 7 134 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 134 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 255 (accept_3_4 4 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 255 (Polychromatic418967fa.accept_24_3_14_15_1_12115 3 134 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 255 (accept_3_4 1 134 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 133 255 (Eq.refl Bool.true) (allA_succ_of_accept 122 133 255 (accept_3_5 122 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 121 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 133 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 120 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 133 255 (accept_3_5 119 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 133 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 117 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 133 255 (accept_3_5 116 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 133 255
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 115 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 133 255 (accept_3_5 113 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 133 255
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 111 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 133 255 (accept_3_5 110 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 109 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 108 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 255 (accept_3_5 107 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 105 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 255 (accept_3_5 104 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 103 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 255 (accept_3_5 101 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 133
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 255
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 99 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 255 (accept_3_5 98 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 97 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 255 (accept_3_5 95 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 93 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 255 (accept_3_5 92 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 255 (accept_3_5 89 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 255 (accept_3_5 86 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 84 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 255 (accept_3_5 83 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 133 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 81 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 255 (accept_3_5 80 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 255 (Polychromatic418967fa.accept_21_16_7_3_1_8093 79 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 255 (accept_3_5 77 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 255
  (Polychromatic418967fa.accept_21_12_7_3_1_4927 75 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 255 (accept_3_5 74 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 255 (accept_3_5 71 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 255 (accept_3_5 68 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 255 (accept_3_5 65 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 255
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 255 (accept_3_5 62 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 61 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 255 (accept_3_5 59 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 57 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 255 (accept_3_5 56 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 255 (accept_3_5 53 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 255 (accept_3_5 50 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 255 (accept_3_5 47 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 255 (accept_3_5 44 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 255 (accept_3_5 41 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 255
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 255 (accept_3_5 38 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 255 (accept_3_5 35 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 255 (accept_3_5 32 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 255 (accept_3_5 29 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 255 (accept_3_5 26 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 255 (accept_3_5 23 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 255 (accept_3_5 20 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 255 (accept_3_5 17 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 255 (accept_3_5 14 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 255 (accept_3_5 11 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 255 (accept_3_5 8 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 255 (accept_3_5 5 133 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 255
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 255 (accept_3_5 2 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 132 255 (Eq.refl Bool.true) (allA_succ_of_gcd 123 132 255 3 41 44 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 132 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 122 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 121 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 255 3 40 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 255 (Polychromatic418967fa.accept_9_2_6_3_1_178
  119 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 132 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 118 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 132 255 3 39 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 116 132 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 132 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 115 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 132 255 3 38 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 113 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  112 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 132 255 3 37 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 110 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 255 3 36 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100
  107 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 106 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 132 255 3 35 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  103 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 255 3 34 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 101 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 132 255 3 33 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 98
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 97 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 255 3 32 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  94 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 132 255 3 31 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 92 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 132 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 255 3 30 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 89
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 88 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 132 255 3 29 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  85 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 132 255 3 28 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 132 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 132 255 3 27 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 255 3 26 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  76 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 132 255 3 25 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 132 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 132 255 3 24 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 132 255 3 23 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271
  67 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 255 3 22 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 132 255 3 21 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 255 3 20 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100
  58 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 132 255 3 19 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 132 255 3 18 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 132 255 3 17 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  49 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 255 3 16 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 132 255 3 15 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 255 3 14 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 132 255 3 13 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 255 3 12 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 35
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 132 255 3 11 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 132 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 255 3 10 44 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 132 255 3 9 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 255 3 8 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 132 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 255 3 7 44 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 255 3 6 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 132 255 3 5 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 132 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 255 3 4 44 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 255 3 3 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 132 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 255 3 2 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 255 3 1 44 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 132 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 131 255 (Eq.refl Bool.true) (allA_succ_of_accept 124 131 255 (accept_3_4 124 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 123 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 122 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 131 255 (accept_3_4 121 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 120 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 131 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 119 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 131 255 (accept_3_4 118 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 131 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 117 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 131 255 (accept_3_4 115 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 113 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 131 255 (accept_3_4 112 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 131 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 111 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 131 255 (accept_3_4 109 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 131 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 107 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 255 (accept_3_4 106 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 105 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 131 255 (accept_3_4 103 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 131 255 (Polychromatic418967fa.accept_13_11_1_8_1_1776 102 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 255 (accept_3_4 100 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 131 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 255 (accept_3_4 97 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 255 (Polychromatic418967fa.accept_22_7_21_13_1_5994 95 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 255 (accept_3_4 94 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 131 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 255 (accept_3_4 91 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 90 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 131 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 255 (accept_3_4 88 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 255 (accept_3_4 85 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 255 (accept_3_4 82 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 255 (accept_3_4 79 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 77 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 255 (accept_3_4 76 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 255 (accept_3_4 73 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 255 (accept_3_4 70 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 255 (accept_3_4 67 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 255 (accept_3_4 64 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 255 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 131 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 255 (accept_3_4 61 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 59 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 255 (accept_3_4 58 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 131 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 255 (accept_3_4 55 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 255 (accept_3_4 52 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 255 (accept_3_4 49 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 255 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 255 (accept_3_4 46 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 255 (accept_3_4 43 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 255 (Polychromatic418967fa.accept_19_3_17_8_1_5916 41 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 255 (accept_3_4 40 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 131
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 255 (accept_3_4 37 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 255 (accept_3_4 34 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 255 (accept_3_4 31 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 255 (accept_3_4 28 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 131 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 255 (accept_3_4 25 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 255 (accept_3_4 22 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 255 (accept_3_4 19 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 255 (accept_3_4 16 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 255 (accept_3_4 13 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 255 (accept_3_4 10 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 255 (accept_3_4 7 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 255 (accept_3_4 4 131 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 255 (Polychromatic418967fa.accept_19_3_17_8_1_5916 3 131 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 255 (accept_3_4 1 131 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 130 255 (Eq.refl Bool.true) (allA_succ_of_gcd 125 130 255 5 25 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 124 130 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 124 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 130 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 123 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 130 255 (accept_3_5 122 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 130 255 5 24 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 130 255 (accept_3_5 119 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 130 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 118 130
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 130 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 130 255 (accept_3_5 116 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  115 130 255 5 23 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 114 130 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 114 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 130 255 (accept_3_5 113 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 130 255 (Polychromatic418967fa.accept_19_17_16_8_1_2099 112 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 130 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 130 255 5 22 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 130 255
  (Polychromatic418967fa.accept_16_12_2_15_1_490 108 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 130 255 (accept_3_5 107 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 130 255 5 21 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 130 255 (accept_3_5 104 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 130 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 102 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 130 255 (accept_3_5 101 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 130 255 5 20 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 130 255 (accept_3_5 98 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 130 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 96 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 130 255 5 19 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 130 255 (Polychromatic418967fa.accept_19_18_16_8_1_12903 94 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 130 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 130 255 (accept_3_5 92 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 130 255 5 18 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 130 255 (accept_3_5 89 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 130 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 130 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 130 255 (accept_3_5 86 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 130 255 5 17 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 130 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 84 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 130 255 (accept_3_5 83 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 130 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 255 5 16 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 130 255 (accept_3_5 77 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 130 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 130 255 5 15 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 130 255 (accept_3_5 74 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 255
  (Polychromatic418967fa.accept_19_15_16_8_1_11553 72 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 130 255 (accept_3_5 71 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 255 5 14 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 255 (accept_3_5 68 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 130 255 5 13 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 255 (Polychromatic418967fa.accept_14_7_4_3_1_488
  63 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 255 (accept_3_5 62
  130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 130 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 255 5 12 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 255 (accept_3_5 59 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 130 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 58 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 255 (accept_3_5 56
  130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 130 255 5 11 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 130 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 255 (accept_3_5 53 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 130 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 130 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 255 5 10 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 130 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 255 (accept_3_5 47 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 130 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 130 255 5 9 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 130 255 (accept_3_5 44 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 255 (accept_3_5 41 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  130 255 5 8 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 130 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 39 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 130 255 (accept_3_5 38 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 130 255 5 7 26 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 130 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 255 (accept_3_5 32 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 255 5 6 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 255 (accept_3_5 29 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 255 (accept_3_5 26 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  130 255 5 5 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 130 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 130 255 (accept_3_5 23 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 130 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 255 5 4 26 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 130 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 255 (accept_3_5 17 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 130 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 130 255 5 3 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 130 255 (accept_3_5 14 130 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 255
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 255 (accept_3_5 11 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  130 255 5 2 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 130 255 (accept_3_5 8 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 130 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 130 255 5 1 26 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 130 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 130 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 130 255 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 255 (accept_3_5 2 130 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 130 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 129 255 (Eq.refl Bool.true) (allA_succ_of_gcd 126 129 255 3 42 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 129 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 125 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 124 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 129 255 3 41 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27
  122 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 121 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 129 255 3 40 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 129 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 119 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 118 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 129 255 3 39 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 129 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 116 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 115 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 129 255 3 38 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 129 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 113 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 129 255
  (Polychromatic418967fa.accept_19_17_15_8_1_5936 112 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 129 255 3 37 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 109 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 129 255 3 36 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 129 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 107 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 129 255 3 35 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 129 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 104 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 103 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 129 255 3 34 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 101 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 255
  (Polychromatic418967fa.accept_13_9_12_8_1_570 100 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 129 255 3 33 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  97 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 129 255 3 32 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 129 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 95 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 129 255 3 31 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 129 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818
  92 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 91 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 129 255 3 30 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 129 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 255
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 88 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 129 255 3 29 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 85 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 129 255 3 28 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 129 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 83 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 129 255 3 27 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 129 255 (Polychromatic418967fa.accept_19_4_15_8_1_5937 80 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 129 255 3 26 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 129 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  76 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 129 255 3 25 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 129 255 3 24 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 71
  129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 129 255 3 23 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 129 255 (Polychromatic418967fa.accept_22_2_19_13_1_10829 68 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 129 255 3 22 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 129 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 255 (Polychromatic418967fa.accept_10_4_9_5_1_84
  64 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 255 3 21 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 255 3 20 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 255 3 19 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 129 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 129 255 3 18 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 129 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 255
  (Polychromatic418967fa.accept_25_2_4_5_1_15586 52 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 129 255 3 17 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 255 (Polychromatic418967fa.accept_11_5_8_2_1_588
  49 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 129 255 3 16 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 129 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 255 3 15 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 44
  129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 255 3 14 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 255
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 255 3 13 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 255 3 12 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 255 3 11 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 255
  (Polychromatic418967fa.accept_22_10_19_13_1_9236 32 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 255 3 10 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 255 (Polychromatic418967fa.accept_22_6_19_13_1_5992 28 129 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 255 3 9 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 255 3 8 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 255 3 7 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 129
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 255 3 6 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 255 3 5 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 255 3 4 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 255 3 3 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 255
  (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 255 3 2 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 129 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 255
  (Polychromatic418967fa.accept_10_4_9_5_1_84 4 129 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 255 3 1 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 129 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 255 (allA_succ_of_accept 127 128 255 (accept_3_4 127 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 128 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 126 128 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 128 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 125 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 128 255 (accept_3_4 124 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 128 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 123 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 128 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 122 128 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 128 255 (accept_3_4 121 128 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 128 255 (accept_3_4 118 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 117 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 128 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 116 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 128 255 (accept_3_4 115 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 114 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 113 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 128 255 (accept_3_4 112 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 111 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 110 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 128 255 (accept_3_4 109 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 128 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 108 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 128 255 (accept_3_4 106 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 105 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 104 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 128 255 (accept_3_4 103 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 128 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 102 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 128 255 (accept_3_4 100 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 128 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 128 255 (accept_3_4 97 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 128 255 (accept_3_4 94 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 128 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 93 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 128 255 (accept_3_4 91 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 128 255 (accept_3_4 88 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 128 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 128 255 (accept_3_4 85 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 128 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 128 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 128 255 (accept_3_4 82 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 128 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 81 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 128 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 128 255 (accept_3_4 79 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 128 255 (accept_3_4 76 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 128 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 74 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 255 (accept_3_4 73 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 128 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 128
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 128 255 (accept_3_4 70 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 128 255 (accept_3_4 67 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 128 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 128 255 (accept_3_4 64 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 128 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 128 255 (accept_3_4 61 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 128 255 (accept_3_4 58 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 128 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 56 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 128 255 (accept_3_4 55 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 128 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 128 255 (accept_3_4 52 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 255 (accept_3_4 49 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 255 (accept_3_4 46 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 255 (accept_3_4 43 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 255 (accept_3_4 40 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 255 (Polychromatic418967fa.accept_21_18_2_3_1_9685 39 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 255 (Polychromatic418967fa.accept_21_17_2_3_1_4942 38 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 255 (accept_3_4 37 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 128 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 255 (accept_3_4 34 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 255 (accept_3_4 31 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 255 (accept_3_4 28 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 255 (accept_3_4 25 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 255 (accept_3_4 22 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 255 (Polychromatic418967fa.accept_19_2_14_8_1_3273 21 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 255 (accept_3_4 19 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 255 (accept_3_4 16 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 255 (accept_3_4 13 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 255 (accept_3_4 10 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 255 (accept_3_4 7 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 128 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 255 (accept_3_4 4 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 128 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 255 (accept_3_4 1 128 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 255 (allA_succ_of_accept 126 127 255 (Polychromatic418967fa.accept_28_14_15_3_1_3400 126 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 255 (accept_3_5 125 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77
  124 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 123 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 127 255 (accept_3_5 122 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 121 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 127 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 120 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 127 255 (accept_3_5 119 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 118 127
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 117 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 255 (accept_3_5 116 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 115 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 255 (accept_3_5 113 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 127
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 255
  (Polychromatic418967fa.accept_13_7_10_8_1_567 111 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 255 (accept_3_5 110 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 127 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 108 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 255 (accept_3_5 107 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 127
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 105 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 255 (accept_3_5 104 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 255 (accept_3_5 101 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 127
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 255
  (Polychromatic418967fa.accept_18_9_1_3_1_6451 99 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 255 (accept_3_5 98 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 255 (accept_3_5 95 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 255 (accept_3_5 92 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 255 (Polychromatic418967fa.accept_21_7_1_3_1_11160 91 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 90 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 255 (accept_3_5 89 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 255 (accept_3_5 86 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 85 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 84 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 255 (accept_3_5 83 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 255 (accept_3_5 80 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 255 (accept_3_5 77 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 255 (accept_3_5 74 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 255 (accept_3_5 71 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 255 (accept_3_5 68 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 66 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 255 (accept_3_5 65 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 255 (accept_3_5 62 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 255 (accept_3_5 59 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 255 (accept_3_5 56 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 255 (Polychromatic418967fa.accept_22_11_17_13_1_9270 55 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 255 (accept_3_5 53 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 255 (accept_3_5 50 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 255 (accept_3_5 47 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 255 (accept_3_5 44 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 255 (accept_3_5 41 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 255 (accept_3_5 38 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 255 (Polychromatic418967fa.accept_21_15_1_3_1_9587 36 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 255 (accept_3_5 35 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 255 (accept_3_5 32 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 255 (accept_3_5 29 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 255
  (Polychromatic418967fa.accept_18_9_1_3_1_6451 27 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 255 (accept_3_5 26 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 255 (accept_3_5 23 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 255 (accept_3_5 20 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 255 (accept_3_5 17 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 255 (accept_3_5 14 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 255 (accept_3_5 11 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 255 (accept_3_5 8 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 255 (accept_3_5 5 127 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 255 (accept_3_5 2 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 255 (Polychromatic418967fa.accept_19_1_13_8_1_8779 1 127 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 255 (allA_succ_of_accept 125 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 125 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 126 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 124 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 126 255 3 41 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 122 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 126 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 121 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 126 255 3 40 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 126 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 119 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 126 255
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 118 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 126 255 3 39 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 126 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 116 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 126 255
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 115 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 255 3 38 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 112 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 126 255 3 37 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 110 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 126 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 255 3 36 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 107 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 126 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 106 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 126 255 3 35 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 104 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 255
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 103 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 255 3 34 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 100 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 126 255 3 33 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 98 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 255 3 32 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 255
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 95 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 94 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 126 255 3 31 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 126 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  92 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 126 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 91 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 255 3 30 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 255 (Polychromatic418967fa.accept_12_4_6_3_1_332
  88 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 126 255 3 29 42 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 126 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 255 3 28 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 255
  (Polychromatic418967fa.accept_19_7_12_8_1_10122 83 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 82 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 126 255 3 27 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 126 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 126 255 3 26 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 76 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 126 255 3 25 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 74 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 126 255 3 24 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 126 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 71 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 126 255 3 23 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 126 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  68 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 255
  (Polychromatic418967fa.accept_19_10_12_8_1_10124 67 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 126 255 3 22 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 64 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 126 255 3 21 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 255 3 20 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 126 255 3 19 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 126 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  56 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 255
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 55 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 255 3 18 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  52 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 126 255 3 17 42 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 126 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 255 3 16 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 255
  (Polychromatic418967fa.accept_22_3_16_13_1_15541 47 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 126 255 3 15 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 126 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 255 (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 255 3 14 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 126 255 3 13 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 255 3 12 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 126 255
  (Polychromatic418967fa.accept_26_9_22_21_1_15585 35 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 126 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 255 3 11 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 255 3 10 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 255 3 9 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 255 3 8 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 255
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 23 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 255 3 7 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 255 3 6 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 126 255 3 5 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 255 3 4 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 255 3 3 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 126 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 255
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 255 3 2 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 126 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 255 3 1 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 255 (allA_succ_of_accept 124 125 255 (accept_3_4 124 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 123 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 125
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 255 (accept_3_4 121 125
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 125 255 5 24 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 125 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 119 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 125 255 (accept_3_4 118 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 125 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 117 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 116 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 115 125 255 5 23 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 125 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 125 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 113 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 255 (accept_3_4 112 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 125 255 (Polychromatic418967fa.accept_19_16_11_8_1_8758 111 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 125 255 5 22 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 125 255 (accept_3_4 109 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 125 255 (Polychromatic418967fa.accept_11_9_4_2_1_600
  108 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 107 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 125 255 (accept_3_4 106 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  105 125 255 5 21 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 104 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 104 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 255 (accept_3_4 103 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 101 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 125 255 5 20 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 125 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 99 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 255 (accept_3_4 97 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 125 255 5 19 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 125 255 (accept_3_4 94 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 125 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 255 (accept_3_4 91 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 125 255 5 18 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 125 255
  (Polychromatic418967fa.accept_20_9_5_15_1_3965 89 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 255 (accept_3_4 88 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 125 255 5 17 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 125 255
  (Polychromatic418967fa.accept_20_4_5_15_1_6869 84 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 125 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 255 (accept_3_4 82 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 125 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 125 255 5 16 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 125 255 (accept_3_4 79 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 255 (accept_3_4 76 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  125 255 5 15 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 255 (accept_3_4 73 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 125 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 255
  (Polychromatic418967fa.accept_20_11_5_15_1_8438 71 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 125 255 5 14 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 125 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 255 (accept_3_4 67 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 125 255 5 13 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 125 255 (accept_3_4 64 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 255 (Polychromatic418967fa.accept_20_3_5_15_1_2644 63 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 255 (accept_3_4 61 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 125 255 5 12 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 125 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 255 (accept_3_4 58 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 125 255 5 11 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 125 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 125 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 255 (accept_3_4 52 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 125 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 125 255 5 10 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 125 255 (accept_3_4 49 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 255 (Polychromatic418967fa.accept_19_10_11_8_1_10121 48
  125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 255 (accept_3_4 46 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  125 255 5 9 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 125 255 (accept_3_4 43 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 255 5 8 25 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 255 (accept_3_4 37 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 255 (Polychromatic418967fa.accept_19_17_11_8_1_11490 36 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 255 5 7 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 255 (accept_3_4 34 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 255 (Polychromatic418967fa.accept_9_6_8_3_1_183
  33 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 255 (accept_3_4 31 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 255 5 6 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 255 (accept_3_4 28 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 255 (Polychromatic418967fa.accept_20_7_5_15_1_1548 27 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 255 5 5 25 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 255 (accept_3_4 22 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 255 5 4 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 255 (accept_3_4 19 125 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 255 (accept_3_4 16 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  125 255 5 3 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 255 (accept_3_4 13 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 255 (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 255 (Polychromatic418967fa.accept_7_4_6_3_1_271
  11 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 255 5 2 25 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 255 (accept_3_4 7 125 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 255 5 1 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 255 (accept_3_4 4 125 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 125 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 255 (accept_3_4 1 125 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 255 (allA_succ_of_accept 123 124 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 123 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 124 255 (accept_3_5 122 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 121 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 124 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 120 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 124 255 (accept_3_5 119 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 124 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 118 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 124 255 (Polychromatic418967fa.accept_14_5_12_3_1_3397 117 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 124 255 (accept_3_5 116 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 124 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 114 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 124 255 (accept_3_5 113 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 124 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 124 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 111 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 124 255 (accept_3_5 110 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 109 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 124 255
  (Polychromatic418967fa.accept_23_16_9_2_1_9078 108 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 124 255 (accept_3_5 107 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 124 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 124 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 105 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 124 255 (accept_3_5 104 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 124 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 103 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 124 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 102 124 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 124 255 (accept_3_5 101 124 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 124 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 124 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 124 255 (accept_3_5 98 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 124 255 (accept_3_5 95 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 124 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 124 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 124 255 (accept_3_5 92 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 124 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 255 (accept_3_5 89 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 124 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 88 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 124 255 (accept_3_5 86 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 124 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 84 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 255 (accept_3_5 83 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 124 255 (accept_3_5 80 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 124 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 255 (accept_3_5 77 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 124 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 75 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 124 255 (accept_3_5 74 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 124 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 255 (accept_3_5 71 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 255 (Polychromatic418967fa.accept_20_10_4_15_1_12657 70 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 255 (accept_3_5 68 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 255 (accept_3_5 65 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 255
  (Polychromatic418967fa.accept_23_17_9_2_1_15584 63 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 124 255 (accept_3_5 62 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 124 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 255 (accept_3_5 59 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 58
  124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 255 (accept_3_5 56 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 255 (accept_3_5 53 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 52 124
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 255 (accept_3_5 50 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 255 (accept_3_5 47 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 255 (accept_3_5 44 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 255 (accept_3_5 41 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 39 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 255 (accept_3_5 38 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 255 (accept_3_5 35 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 255 (accept_3_5 32 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 255 (accept_3_5 29 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 255 (accept_3_5 26 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 255 (accept_3_5 23 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 255 (accept_3_5 20 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 255 (accept_3_5 17 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 255 (accept_3_5 14 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 255 (accept_3_5 11 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 124 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 255 (accept_3_5 8 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 255 (accept_3_5 5 124 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 124 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 255 (accept_3_5 2 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 123 255 (allA_succ_of_accept 122 123 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 122 123 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 121 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 123 255 3 40 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 119 123 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 118 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 123 255 3 39 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 123 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 116 123 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 115 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 123 255 3 38 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 113 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  112 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 123 255 3 37 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 123 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 110 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 123 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 109 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 123 255 3 36 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457
  107 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 106 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 123 255 3 35 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 104 123 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 103 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 123 255 3 34 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 101 123 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 100 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 123 255 3 33 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 98 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  97 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 123 255 3 32 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 95 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 123 255 3 31 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 92
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 91 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 123 255 3 30 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  88 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 123 255 3 29 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 123 255 3 28 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 83
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 123 255 3 27 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  79 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 123 255 3 26 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 123 255 3 25 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 255 3 24 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 123 255 3 23 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 123 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 68 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 123 255 3 22 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 255 3 21 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 255 3 20 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 255 3 19 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 255 3 18 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 255 (Polychromatic418967fa.accept_8_4_3_7_1_491
  52 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 255 3 17 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 255 3 16 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 255 3 15 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 255 3 14 41 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 123 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 255 3 13 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 123 255 3 12 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 123 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  34 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 255 3 11 41 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 255 3 10 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 255 3 9 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 123 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 255 3 8 41 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 255 3 7 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 123 255 3 6 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 123 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 255 3 5 41 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 255 3 4 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 123 255 3 3 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 123 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 255 3 2 41 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 123 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 255 3 1 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 255 (allA_succ_of_accept 121 122 255 (accept_3_4 121 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 120 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 255 (Polychromatic418967fa.accept_6_5_2_3_1_81
  119 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 255 (accept_3_4
  118 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 116 122 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 255 (accept_3_4 115 122 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 114 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 255 (accept_3_4 112 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 111 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 110 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 255 (accept_3_4 109 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 108 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 255 (accept_3_4 106 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 104 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 255 (accept_3_4 103 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 102 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 255 (accept_3_4 100 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 99 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 98 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 255 (accept_3_4 97 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 255 (accept_3_4 94 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 255 (accept_3_4 91 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 255 (accept_3_4 88 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 255 (Polychromatic418967fa.accept_21_2_17_3_1_9644 86 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 255 (accept_3_4 85 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 255 (Polychromatic418967fa.accept_18_12_14_3_1_2655 84 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 255 (accept_3_4 82 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 80 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 255 (accept_3_4 79 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 255 (accept_3_4 76 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 75 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 255 (accept_3_4 73 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 255 (Polychromatic418967fa.accept_21_9_17_3_1_6408 72 122 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 255 (accept_3_4 70 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 68 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 255 (accept_3_4 67 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 255 (accept_3_4 64 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 255 (accept_3_4 61 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 255 (accept_3_4 58 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 255 (accept_3_4 55 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 122 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 255 (accept_3_4 52 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 255 (Polychromatic418967fa.accept_20_10_2_15_1_1517 50 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 255 (accept_3_4 49 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 255 (accept_3_4 46 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 255 (accept_3_4 43 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 255 (accept_3_4 40 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 255 (Polychromatic418967fa.accept_21_18_17_3_1_4906 39 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 255 (accept_3_4 37 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 255 (accept_3_4 34 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 255 (accept_3_4 31 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 255 (accept_3_4 28 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 255 (accept_3_4 25 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 255 (accept_3_4 22 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 255 (accept_3_4 19 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 255 (accept_3_4 16 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 255 (accept_3_4 13 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 122
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 255 (accept_3_4 10 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 255 (accept_3_4 7 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 122 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 255 (accept_3_4 4 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 122 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 255 (accept_3_4 1 122 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 255 (allA_succ_of_accept 120 121 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 255 (accept_3_5 119 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 121
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 117 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 255 (accept_3_5 116 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 115 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 255 (accept_3_5 113 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 121
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 255 (accept_3_5 110 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 109 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 255 (Polychromatic418967fa.accept_22_20_11_13_1_15583 108 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 255 (accept_3_5 107 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 105 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 255 (accept_3_5 104 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 255 (accept_3_5 101 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 121
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 255 (accept_3_5 98 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 255 (accept_3_5 95 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 93 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 255 (accept_3_5 92 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 255 (accept_3_5 89 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 255 (accept_3_5 86 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 255 (accept_3_5 83 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 81 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 255 (accept_3_5 80 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 255 (accept_3_5 77 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 255 (accept_3_5 74 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 255 (Polychromatic418967fa.accept_16_8_9_15_1_5112 72 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 255 (accept_3_5 71 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 255 (accept_3_5 68 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 255 (Polychromatic418967fa.accept_20_7_1_15_1_2700 67 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 255 (accept_3_5 65 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 255 (accept_3_5 62 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 255 (accept_3_5 59 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 255 (accept_3_5 56 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 255 (accept_3_5 53 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 255 (accept_3_5 50 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 255 (accept_3_5 47 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 255 (accept_3_5 44 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 255 (accept_3_5 41 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 255 (accept_3_5 38 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 255 (accept_3_5 35 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 255 (accept_3_5 32 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 255 (Polychromatic418967fa.accept_19_12_7_8_1_12860 31 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 255 (accept_3_5 29 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 255 (accept_3_5 26 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 255 (accept_3_5 23 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 255 (accept_3_5 20 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 255 (accept_3_5 17 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 255 (accept_3_5 14 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 255 (accept_3_5 11 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 255 (accept_3_5 8 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 255 (accept_3_5 5 121 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 255
  (Polychromatic418967fa.accept_22_3_11_13_1_9262 3 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 255 (accept_3_5 2 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 255 (allA_succ_of_accept 119 120 255 (Polychromatic418967fa.accept_16_7_8_15_1_6327 119 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 255
  (Polychromatic418967fa.accept_23_3_5_2_1_15582 118 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 117 120 255 3 39 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 116 120 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 116 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 115 120 255 5 23 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 120 255 3 38 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 255
  (Polychromatic418967fa.accept_13_9_3_8_1_573 113 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 120 255 (Polychromatic418967fa.accept_19_17_6_8_1_5928 112 120 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 120 255 3 37 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 120 255 5 22 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 109 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 255 3 36 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 255
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 106 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 120 255 15 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 120 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103 104 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 103 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 255 3 34 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 255 (Polychromatic418967fa.accept_21_17_15_3_1_4937 101 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 255 5 20 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 120 255 3 33 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 120 255
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 98 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 255 (Polychromatic418967fa.accept_16_1_8_15_1_1945 97 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 255 3 32 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 120 255 5 19 24 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 120 255
  (Polychromatic418967fa.accept_21_10_15_3_1_6431 94 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 120 255 3 31 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 120 255 (Polychromatic418967fa.accept_16_12_8_15_1_5119 92 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 120 255
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 91 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 255 15 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 120 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 120 255 3 29 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 120 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 120 255 5 17 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 120 255 3 28 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 120 255 (Polychromatic418967fa.accept_13_5_3_8_1_1117 83 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 82 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 120 255 3 27 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 120 255 5 16 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 255 3 26 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 255
  (Polychromatic418967fa.accept_21_14_15_3_1_9580 77 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 120 255 (Polychromatic418967fa.accept_13_11_3_8_1_1786 76 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 120 255 15 5 8 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 120 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 255 (Polychromatic418967fa.accept_16_9_8_15_1_5095 73 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 255 3 24 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 255 (Polychromatic418967fa.accept_16_7_8_15_1_6327
  71 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 255 5 14 24 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 120 255 3 23 40
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 120 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 255 3 22 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 120 255 5 13 24 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 120 255
  (Polychromatic418967fa.accept_19_7_6_8_1_12854 64 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 120 255 3 21 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 120 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 62 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 255 15 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 120 255 (Polychromatic418967fa.accept_13_7_3_8_1_1750 59 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 120 255 3 19 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 120 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 56 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 120 255 5 11 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 120 255 3 18 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 120 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 255
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 120 255 3 17 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 120 255 5 10 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 120 255 (Polychromatic418967fa.accept_16_1_8_15_1_1945 49 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 255 3 16 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 120 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 255 15 3 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 255
  (Polychromatic418967fa.accept_18_7_12_3_1_804 43 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 255 3 14 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 255 (Polychromatic418967fa.accept_16_9_8_15_1_5095 41 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 255 5 8 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 255 3 13 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 255
  (Polychromatic418967fa.accept_18_2_12_3_1_2707 38 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 255 3 12 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 255 5 7 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 255 (Polychromatic418967fa.accept_11_1_10_2_1_58
  34 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 120 255 3 11 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 120 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 255 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 255 15 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 255 (Polychromatic418967fa.accept_21_8_15_3_1_279
  29 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 255
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 120 255 3 9 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 120 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 120 255 5 5 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 255 3 8 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 255 3 7 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 255 5 4 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19
  120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 255 3 6 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 255
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 255 15 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 255
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 255 (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 120 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 255 3 4 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 255 5 2 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 120 255 3 3 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 120 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 8 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 255 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 255 3 2 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 255 5 1 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 120 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 120 255 3 1 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 120 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 120 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 120 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 255 (allA_succ_of_accept 118 119 255 (accept_3_4 118 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 117 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 116 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 255 (accept_3_4 115 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 114 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 113 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 255 (accept_3_4 112 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 111 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 255 (accept_3_4 109 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 255 (Polychromatic418967fa.accept_14_10_7_3_1_1022 108 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 255 (accept_3_4 106 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 105 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 255 (accept_3_4 103 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  102 119 255 17 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 101 119 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 101 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 255 (accept_3_4 100 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 119 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 99 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 255 (accept_3_4 97 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 95 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 255 (accept_3_4 94 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 255 (accept_3_4 91 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 255 (Polychromatic418967fa.accept_19_14_5_8_1_10077 90 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 255 (accept_3_4 88 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 119 255 17 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 119 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 83 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 255 (accept_3_4 82 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 255 (accept_3_4 79 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194
  77 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 255 (accept_3_4 76
  119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 255
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 75 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 255 (accept_3_4 73 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 119 255 (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 255 (accept_3_4 70 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 119 255 17 4 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 119 255 (accept_3_4 67 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 119 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 66 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 255 (Polychromatic418967fa.accept_20_5_19_15_1_3946 65 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 255 (accept_3_4 64 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 255
  (Polychromatic418967fa.accept_25_13_19_5_1_15581 63 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 255 (accept_3_4 61 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 255 (accept_3_4 58 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 255 (accept_3_4 55 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 255 (accept_3_4 52 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51
  119 255 17 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 119 255 (accept_3_4 49 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 119 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 255 (Polychromatic418967fa.accept_25_22_19_5_1_6512 47 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 255 (accept_3_4 46 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 255 (accept_3_4 43 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194
  41 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 255 (accept_3_4 40
  119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 255
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 255 (accept_3_4 37 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 119 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 119 255 17 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 255 (accept_3_4 31 119 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 255
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 255 (accept_3_4 28 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 255 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 255 (accept_3_4 25 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 255 (accept_3_4 22 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 255 (accept_3_4 19 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 119 255 17 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 119 255 (accept_3_4 16 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 255 (accept_3_4 13 119 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 255
  (Polychromatic418967fa.accept_19_12_5_8_1_7294 12 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 255 (accept_3_4 10 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 255 (accept_3_4 7 119
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 255 (accept_3_4 4 119 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 119 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 255 (accept_3_4 1 119 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 255 (allA_succ_of_accept 117 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 255 (accept_3_5 116 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 118
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 114 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 255 (accept_3_5 113 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 112 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 111 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 255 (accept_3_5 110 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 255
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 108 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 118 255 (accept_3_5 107 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 118 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 118 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 255 (accept_3_5 104 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14
  103 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 102 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 255 (accept_3_5 101 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 255 (Polychromatic418967fa.accept_22_11_8_13_1_15580 99 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 255 (accept_3_5 98 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 96 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 255 (accept_3_5 95 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 255 (accept_3_5 92 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 255 (accept_3_5 89 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 255 (accept_3_5 86 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 255
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 255 (accept_3_5 83 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 255 (accept_3_5 80 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 78 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 255 (accept_3_5 77 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 255 (Polychromatic418967fa.accept_19_18_4_8_1_3282 75 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 255 (accept_3_5 74 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 255 (accept_3_5 71 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 255 (accept_3_5 68 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 255 (accept_3_5 65 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 64 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 255 (accept_3_5 62 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 255 (accept_3_5 59 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 255 (accept_3_5 56 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 255 (accept_3_5 53 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 255 (accept_3_5 50 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 255
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 255 (accept_3_5 47 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 255 (accept_3_5 44 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 255 (accept_3_5 41 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 255 (accept_3_5 38 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 255
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 36 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 255 (accept_3_5 35 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 255 (accept_3_5 32 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 255 (accept_3_5 29 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 255 (Polychromatic418967fa.accept_19_9_4_8_1_8805 28 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 255 (accept_3_5 26 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 255 (accept_3_5 23 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 255 (accept_3_5 20 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 255 (accept_3_5 17 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 255 (accept_3_5 14 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 255 (accept_3_5 11 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 255 (accept_3_5 8 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 255 (accept_3_5 5 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 118 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 255 (accept_3_5 2 118 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 255 (allA_succ_of_accept 116 117 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 116 117 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 115 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 117 255 3 38 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 113 117 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 112 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 117 255 3 37 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  109 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 117 255 3 36 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 117 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 107 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 117 255 3 35 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 117 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 104 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 117 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 103 117 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 117 255 3 34 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 117 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 101 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 117 255 3 33 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 98
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 255
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 97 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 117 255 3 32 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 117 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 95 117 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 117 255 3 31 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 255 (Polychromatic418967fa.accept_12_7_9_3_1_767
  91 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 117 255 3 30 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 89 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 88 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 117 255 3 29 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 117 255 3 28 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 117 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 83 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 117 255 3 27 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 117 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 80 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 255 3 26 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 77
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 255
  (Polychromatic418967fa.accept_21_13_12_3_1_8028 76 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 117 255 3 25 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 73 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 255 3 24 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 117 255 3 23 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 117 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 68 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 255 3 22 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 65
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 255 3 21 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 255 3 20 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 255 3 19 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825
  56 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 255 3 18 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 117 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 255 (Polychromatic418967fa.accept_10_2_7_5_1_605
  52 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 255 3 17 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 255 3 16 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 255 3 15 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 255 3 14 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 255 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 255 3 13 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 255 3 12 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 117 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 255 3 11 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 117 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  31 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 255 3 10 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 255 3 9 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 255 3 8 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 255 3 7 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 255
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 255 3 6 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 255 3 5 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 117
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 255 3 4 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 255 3 3 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 255 3 2 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 4 117
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 255 3 1 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 255 (allA_succ_of_accept 115 116 255 (accept_3_4 115 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 114 116 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 113 116
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 255 (accept_3_4 112 116
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 110 116 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 255 (accept_3_4 109 116 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 255 (Polychromatic418967fa.accept_13_4_12_8_1_197 108 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 255 (accept_3_4 106 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 105 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 104 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 255 (accept_3_4 103 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 116
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 255 (accept_3_4 100 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 98 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 255 (accept_3_4 97 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 116 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 255 (accept_3_4 94 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 255 (Polychromatic418967fa.accept_30_3_26_15_1_15579 93 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 92 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 255 (accept_3_4 91 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 116 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 255 (accept_3_4 88 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 86 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 255 (accept_3_4 85 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 255 (accept_3_4 82 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 81 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 255 (Polychromatic418967fa.accept_22_14_6_13_1_10881 80 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 255 (accept_3_4 79 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 116 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 255 (accept_3_4 76 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 255 (accept_3_4 73 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 255 (accept_3_4 70 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 255 (accept_3_4 67 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 255 (accept_3_4 64 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 255 (Polychromatic418967fa.accept_14_7_4_3_1_488 63 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 255 (accept_3_4 61 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 255 (accept_3_4 58 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 255 (accept_3_4 55 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 255 (accept_3_4 52 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 255 (accept_3_4 49 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 255 (accept_3_4 46 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 255 (Polychromatic418967fa.accept_18_9_8_3_1_2702 45 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 255 (accept_3_4 43 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 255 (accept_3_4 40 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 255 (accept_3_4 37 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 255 (accept_3_4 34 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 255 (accept_3_4 31 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 255 (accept_3_4 28 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 255 (accept_3_4 25 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 255 (accept_3_4 22 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 255 (accept_3_4 19 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 255 (accept_3_4 16 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 255 (accept_3_4 13 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 255 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 116 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 255 (accept_3_4 10 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 255 (accept_3_4 7 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 116 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 255 (accept_3_4 4 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 116 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 255 (accept_3_4 1 116 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 255 (allA_succ_of_accept 114 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 114 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 255 (accept_3_5 113 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 115
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 255
  (Polychromatic418967fa.accept_19_16_1_8_1_3244 111 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 115 255 5 22 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 115 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 109 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 108 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 115 255 (accept_3_5 107 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 115 255 5 21 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 115 255 (accept_3_5 104 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 115 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 103 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 255 (Polychromatic418967fa.accept_18_12_7_3_1_2666 102
  115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 255 (accept_3_5 101
  115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 115 255 5 20 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 115 255
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 99 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 255 (accept_3_5 98 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 97 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 115 255 5 19 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 94 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 115 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 93 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 255 (accept_3_5 92 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 115 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 115 255 5 18 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 115 255 (accept_3_5 89 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 255 (accept_3_5 86 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  115 255 5 17 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 115 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 255 (accept_3_5 83 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 115 255 5 16 23 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 115 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 79 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 255 (accept_3_5 77 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 115 255 5 15 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 115 255 (accept_3_5 74 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 255
  (Polychromatic418967fa.accept_19_15_1_8_1_4520 72 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 255 (accept_3_5 71 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  115 255 5 14 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 255 (accept_3_5 68 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 115 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 66 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 115 255 5 13 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  63 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 255 (accept_3_5 62
  115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 255
  (Polychromatic418967fa.accept_13_9_11_8_1_195 61 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 115 255 5 12 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 115 255 (accept_3_5 59 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 115
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 255 (accept_3_5 56 115
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 115 255 5 11 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 115 255
  (Polychromatic418967fa.accept_19_16_1_8_1_3244 54 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 255 (accept_3_5 53 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 115 255 5 10 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 115 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 115 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 255 (accept_3_5 47 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 115 255 5 9 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 255 (accept_3_5 44 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 115
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 255 (accept_3_5 41 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  115 255 5 8 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 115 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 115 255 (accept_3_5 38 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 115 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 255 5 7 23 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 255 (accept_3_5 32 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 255 5 6 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 255 (accept_3_5 29 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 255 (accept_3_5 26 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  115 255 5 5 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 255 (accept_3_5 23 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 115
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 255 5 4 23 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 255 (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 255 (accept_3_5 17 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 255 5 3 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 255 (accept_3_5 14 115 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 255 (accept_3_5 11 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 255 5 2 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 255 (accept_3_5 8 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 255 5 1 23 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 255 (accept_3_5 2 115 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 115 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 255 (allA_succ_of_accept 113 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 112 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 114 255 3 37 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 114 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 110 114 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 255 3 36 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 107 114 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 106 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 114 255 3 35 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 114 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 104 114 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 114 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 103 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 255 3 34 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  100 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 114 255 3 33 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 114 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 98 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 255 3 32 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 95
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 94 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 114 255 3 31 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 114 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  91 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 114 255 3 30 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 88 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 114 255 3 29 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 86
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 255 3 28 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 255 (Polychromatic418967fa.accept_7_5_2_3_1_106
  82 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 114 255 3 27 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 114 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 80 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 114 255 3 26 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 114 255 3 25 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 114 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 74 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 114 255 3 24 38 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 114 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 70 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 114 255 3 23 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 114 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 255 3 22 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 255 (Polychromatic418967fa.accept_7_1_2_3_1_257
  64 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 114 255 3 21 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 114 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 255 3 20 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 114 255 3 19 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 114 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  55 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 255 3 18 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 114 255 3 17 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 114 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 255 3 16 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 255 3 15 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 255 3 14 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 114 255 3 13 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 114 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 255 3 12 38 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 255 3 11 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 255 3 10 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 255 3 9 38 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 255 3 8 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 114 255 3 7 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 114 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 255 3 6 38 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 255 3 5 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 255 3 4 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 114 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 255 3 3 38 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 255 3 2 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 114 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 114 255 3 1 38 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 114 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 114 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 255 (allA_succ_of_accept 112 113 255 (accept_3_4 112 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 111 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27
  110 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 255 (accept_3_4
  109 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 255
  (Polychromatic418967fa.accept_10_8_3_5_1_613 108 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 113 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 255 (accept_3_4 106 113 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 105 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 255 (accept_3_4 103 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 255 (accept_3_4 100 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 255 (Polychromatic418967fa.accept_19_4_18_8_1_10117 99 113
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 255 (accept_3_4 97 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 255 (accept_3_4 94 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 255 (accept_3_4 91 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 255 (accept_3_4 88 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 255 (accept_3_4 85 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 255 (Polychromatic418967fa.accept_24_12_17_15_1_12084 84 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 255 (accept_3_4 82 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 113 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 255 (accept_3_4 79 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 255 (accept_3_4 76 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 113 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 255 (accept_3_4 73 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 255 (accept_3_4 70 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 255 (accept_3_4 67 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 255 (accept_3_4 64 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 113 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 255 (accept_3_4 61 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 255 (Polychromatic418967fa.accept_13_7_9_8_1_188 59 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 255 (accept_3_4 58 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 113
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 255 (accept_3_4 55 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 255 (accept_3_4 52 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 255 (accept_3_4 49 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 255 (accept_3_4 46 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 255 (accept_3_4 43 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 255 (Polychromatic418967fa.accept_25_16_13_5_1_4699 41 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 255 (accept_3_4 40 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 113 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 255 (accept_3_4 37 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 255 (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 255 (accept_3_4 34 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 255 (accept_3_4 31 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 255 (accept_3_4 28 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 255 (accept_3_4 25 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 255 (accept_3_4 22 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 255 (accept_3_4 19 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 255 (accept_3_4 16 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 255 (accept_3_4 13 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 255 (accept_3_4 10 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 255 (accept_3_4 7 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 255 (accept_3_4 4 113 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 113 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 255 (accept_3_4 1 113 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 255 (allA_succ_of_accept 111 112 255 (Polychromatic418967fa.accept_19_16_17_8_1_8762 111 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 255 (accept_3_5 110 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14
  109 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 108 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 255 (accept_3_5 107 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 106 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 255 (accept_3_5 104 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 112
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 102 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 255 (accept_3_5 101 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 112 255 (Polychromatic418967fa.accept_19_4_17_8_1_2103 99 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 255 (accept_3_5 98 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 96 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 112 255 (accept_3_5 95 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 112 255 (Polychromatic418967fa.accept_21_10_7_3_1_4884 94 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 112 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 93 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 255 (accept_3_5 92 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 90 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 112 255 (accept_3_5 89 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 255 (accept_3_5 86 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 112 255
  (Polychromatic418967fa.accept_22_18_2_13_1_12495 84 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 112 255 (accept_3_5 83 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 112 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 255 (Polychromatic418967fa.accept_22_15_2_13_1_10871 81
  112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 255 (accept_3_5 80
  112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 112 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 255 (accept_3_5 77 112 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 112 255 (Polychromatic418967fa.accept_22_10_2_13_1_5964 76 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 255
  (Polychromatic418967fa.accept_21_12_7_3_1_4927 75 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 255 (accept_3_5 74 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 255 (Polychromatic418967fa.accept_19_15_17_8_1_10101 72 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 255 (accept_3_5 71 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 255 (accept_3_5 68 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 255 (accept_3_5 65 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 63 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 255 (accept_3_5 62 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 255 (accept_3_5 59 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 255
  (Polychromatic418967fa.accept_10_7_2_5_1_298 57 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 255 (accept_3_5 56 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 255 (accept_3_5 53 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 255 (accept_3_5 50 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 255 (accept_3_5 47 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 255
  (Polychromatic418967fa.accept_20_5_12_15_1_9860 45 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 112 255 (accept_3_5 44 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 255 (accept_3_5 41 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 255
  (Polychromatic418967fa.accept_22_18_2_13_1_12495 40 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 255 (Polychromatic418967fa.accept_26_13_8_21_1_15578 39 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 255 (accept_3_5 38 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 255
  (Polychromatic418967fa.accept_21_15_7_3_1_4886 36 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 255 (accept_3_5 35 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 255 (accept_3_5 32 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 255 (accept_3_5 29 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 255 (accept_3_5 26 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 255 (accept_3_5 23 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 255 (Polychromatic418967fa.accept_19_3_17_8_1_5916 22 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 255 (Polychromatic418967fa.accept_22_21_2_13_1_15577 21 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 255 (accept_3_5 20 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 255 (accept_3_5 17 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 255 (accept_3_5 14 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 255
  (Polychromatic418967fa.accept_21_12_7_3_1_4927 12 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 255 (accept_3_5 11 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 255 (Polychromatic418967fa.accept_19_9_17_8_1_2075 9 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 255 (accept_3_5 8 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 255 (accept_3_5 5 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 255 (Polychromatic418967fa.accept_19_4_17_8_1_2103 4 112 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 255 (accept_3_5 2 112 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 255 (allA_succ_of_accept 110 111 255 (Polychromatic418967fa.accept_19_15_16_8_1_11553 110 111 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 109 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 111 255 3 36 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 107 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 106 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 111 255 3 35 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 111 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 104 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 255
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 103 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 111 255 3 34 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 111 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 101 111 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 100 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 111 255 3 33 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 111 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 255
  (Polychromatic418967fa.accept_21_13_6_3_1_3381 97 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 111 255 3 32 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  94 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 111 255 3 31 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 111 255
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 92 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 111 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 111 255 3 30 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 111 255 (Polychromatic418967fa.accept_10_9_1_5_1_594
  89 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 88 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 111 255 3 29 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 255
  (Polychromatic418967fa.accept_19_9_16_8_1_2097 85 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 111 255 3 28 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 111 255 (Polychromatic418967fa.accept_19_7_16_8_1_8761 83 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 255
  (Polychromatic418967fa.accept_19_6_16_8_1_10116 82 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 111 255 3 27 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 111 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 111 255 3 26 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 111 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 77 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 255 3 25 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 255
  (Polychromatic418967fa.accept_20_13_11_15_1_6881 73 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 111 255 3 24 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 111 255 (Polychromatic418967fa.accept_21_8_6_3_1_4881 71 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 255
  (Polychromatic418967fa.accept_20_10_11_15_1_6885 70 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 111 255 3 23 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 111 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 68 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 255 3 22 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  64 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 255 3 21 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 255
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 62 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 61 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 255 3 20 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 255 (Polychromatic418967fa.accept_10_9_1_5_1_594
  59 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 255 3 19 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 255
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 55 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 255 3 18 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 255
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 52 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 111 255 3 17 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 111 255 (Polychromatic418967fa.accept_20_10_11_15_1_6885 50 111 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 49 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 255 3 16 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 255 3 15 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 255 3 14 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 255 (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 255
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 255 3 13 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 38 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 255 3 12 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 111 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 255 3 11 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 255
  (Polychromatic418967fa.accept_22_9_1_13_1_7731 31 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 255 3 10 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 255 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  28 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 255 3 9 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 255 3 8 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 255
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 255 3 7 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 20 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 255 (Polychromatic418967fa.accept_10_9_1_5_1_594
  19 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 255 3 6 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 255
  (Polychromatic418967fa.accept_19_17_16_8_1_2099 17 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 255 3 5 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 255 (Polychromatic418967fa.accept_20_13_11_15_1_6881 13 111 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 255 3 4 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 255 3 3 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 255 (Polychromatic418967fa.accept_21_8_6_3_1_4881 8 111 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 255
  (Polychromatic418967fa.accept_19_7_16_8_1_8761 7 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 255 3 2 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 255 (Polychromatic418967fa.accept_19_5_16_8_1_10057 5 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 255 3 1 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 111 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 255 (allA_succ_of_accept 109 110 255 (accept_3_4 109 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 255 (Polychromatic418967fa.accept_20_8_10_15_1_6922 108 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 255 (Polychromatic418967fa.accept_6_5_2_3_1_81
  107 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 255 (accept_3_4
  106 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 110 255 5 21 22 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 110 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 104 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 110 255 (accept_3_4 103 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 110 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 102 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 255 5 20 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 110 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 255 (accept_3_4 97 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 110 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 110 255 5 19 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 110 255 (accept_3_4 94 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 110 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 92 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 110 255 (accept_3_4 91 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  110 255 5 18 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 110 255 (accept_3_4 88 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 110 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 110 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 86
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 110 255 5 17 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 110 255
  (Polychromatic418967fa.accept_16_4_14_15_1_6331 84 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 110 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 110 255 (accept_3_4 82 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 110 255 5 16 22 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 110 255 (accept_3_4 79 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  78 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 255 (accept_3_4 76 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  110 255 5 15 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 110 255 (Polychromatic418967fa.accept_16_10_14_15_1_2933 74 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 255 (accept_3_4 73 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 255 5 14 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 255 (Polychromatic418967fa.accept_9_5_2_3_1_194
  68 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 255 (accept_3_4 67
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 66 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 110 255 5 13 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 110 255 (accept_3_4 64 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 110 255 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 255 (accept_3_4 61 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 110 255 5 12 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 110 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 255 (accept_3_4 58 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 255 (Polychromatic418967fa.accept_20_16_10_15_1_5368 56 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 110 255 5 11 22 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 110 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 255 (accept_3_4 52 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 110 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 110 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 255 5 10 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 255 (accept_3_4 49 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 255 (Polychromatic418967fa.accept_18_12_2_3_1_6414 48 110
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 255 (accept_3_4 46 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  110 255 5 9 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 110 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 110 255 (accept_3_4 43 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 110 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 255 5 8 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 255
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 39 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 255 (Polychromatic418967fa.accept_20_18_10_15_1_3937 38 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 255 (accept_3_4 37 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 110 255 5 7 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 110 255 (accept_3_4 34
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 110 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 255 (accept_3_4 31 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 110 255 5 6 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 255 (accept_3_4 28 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 110
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 110 255 5 5 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 110 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 255 (accept_3_4 22 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 255 5 4 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 255 (accept_3_4 19
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 255 (accept_3_4 16 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 110 255 5 3 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 110 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 255 (accept_3_4 13 110 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 255 (Polychromatic418967fa.accept_18_12_2_3_1_6414 12 110
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 255 5 2 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 255 (accept_3_4 7 110 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 255 5 1 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 255 (accept_3_4 4
  110 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 255
  (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 110 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 110 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 255 (accept_3_4 1 110 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 110
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 255 (allA_succ_of_accept 108 109 255 (Polychromatic418967fa.accept_16_12_13_15_1_1966 108 109 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 255 (accept_3_5 107 109 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27
  106 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 105 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 255 (accept_3_5 104 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 103 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 255 (accept_3_5 101 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 109
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 255 (accept_3_5 98 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 255 (accept_3_5 95 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 93 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 255 (accept_3_5 92 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 255 (accept_3_5 89 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 255 (accept_3_5 86 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 255 (accept_3_5 83 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 255 (accept_3_5 80 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 255 (accept_3_5 77 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 255
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 75 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 255 (accept_3_5 74 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 255 (Polychromatic418967fa.accept_22_7_21_13_1_5994 73 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 255 (Polychromatic418967fa.accept_30_12_19_15_1_15576 72 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 255 (accept_3_5 71 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 255 (accept_3_5 68 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 255 (accept_3_5 65 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 255
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 255 (accept_3_5 62 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 255 (accept_3_5 59 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 255 (accept_3_5 56 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 255 (accept_3_5 53 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 255 (accept_3_5 50 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 255 (accept_3_5 47 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 255 (accept_3_5 44 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 255 (accept_3_5 41 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 255
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 39 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 255 (accept_3_5 38 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 255 (Polychromatic418967fa.accept_25_12_9_5_1_15575 37 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 255 (accept_3_5 35 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 255 (accept_3_5 32 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 255 (accept_3_5 29 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 255 (accept_3_5 26 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 255 (accept_3_5 23 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 255 (accept_3_5 20 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 19 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 255 (accept_3_5 17 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 255 (accept_3_5 14 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 255 (accept_3_5 11 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 255 (accept_3_5 8 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 255 (accept_3_5 5 109 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 255 (accept_3_5 2 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 255 (allA_succ_of_accept 107 108 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 107 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 106 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 108 255 3 35 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 108 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 104 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 103 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 255 3 34 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 101 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 255
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 100 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 108 255 3 33 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 108 255 (Polychromatic418967fa.accept_16_2_12_15_1_2908 98 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 97 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 255 3 32 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 95 108 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 255
  (Polychromatic418967fa.accept_19_18_13_8_1_10099 94 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 108 255 3 31 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 92 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 91 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 255 3 30 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 89 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 255
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 88 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 108 255 3 29 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 108 255 (Polychromatic418967fa.accept_25_11_8_5_1_4696 86 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 255
  (Polychromatic418967fa.accept_20_5_8_15_1_9845 85 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 255 3 28 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 108 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  82 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 108 255 3 27 36 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 108 255
  (Polychromatic418967fa.accept_19_4_13_8_1_11544 80 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 108 255 (Polychromatic418967fa.accept_19_3_13_8_1_4476 79 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 108 255 3 26 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 108 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 108 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 76 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 108 255 3 25 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 108 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752
  74 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 73 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 255 3 24 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 255 (Polychromatic418967fa.accept_19_14_13_8_1_5943 71 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 70 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 108 255 3 23 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 108 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 68 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 67 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 255 3 22 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 255 (Polychromatic418967fa.accept_20_5_8_15_1_9845 65 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 255
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 64 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 108 255 3 21 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 62 108 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752
  61 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 255 3 20 36 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 255 (Polychromatic418967fa.accept_19_1_13_8_1_8779 58 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 108 255 3 19 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 108 255
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 108 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 55 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 255 3 18 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 53 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 108 255 3 17 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 108 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098
  50 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 255
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 255 3 16 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 255
  (Polychromatic418967fa.accept_30_16_18_15_1_15574 46 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 108 255 3 15 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 108 255 (Polychromatic418967fa.accept_19_6_13_8_1_4508 44 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 255 3 14 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 41 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 40 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 108 255 3 13 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 108 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 255 3 12 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 255
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 108 255 3 11 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 108 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 255
  (Polychromatic418967fa.accept_23_8_16_2_1_15573 31 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 255 3 10 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 255
  (Polychromatic418967fa.accept_22_6_20_13_1_10914 28 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 108 255 3 9 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 108 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 108 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 255
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 255 3 8 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 108
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 255 3 7 36 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 255
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 255 3 6 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008
  17 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 255
  (Polychromatic418967fa.accept_25_16_8_5_1_15572 16 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 108 255 3 5 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 108 255 (Polychromatic418967fa.accept_19_14_13_8_1_5943 14 108 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 255 3 4 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 108
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 255 3 3 36 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 255
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 255 3 2 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 255 (Polychromatic418967fa.accept_19_5_13_8_1_3229 5 108 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 108 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 108 255 3 1 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 108 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 108 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 255 (Polychromatic418967fa.accept_19_1_13_8_1_8779 1 108
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 255 (allA_succ_of_accept 106 107 255 (accept_3_4 106 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 105 107 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 104 107
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 255 (accept_3_4 103 107
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 102 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 101 107 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 255 (accept_3_4 100 107 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 98
  107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 255 (accept_3_4 97
  107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 107 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 255 (accept_3_4 94 107 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 255 (accept_3_4 91 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 255 (accept_3_4 88 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 255 (accept_3_4 85 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 255 (accept_3_4 82 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 255 (accept_3_4 79 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 255 (accept_3_4 76 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 255 (accept_3_4 73 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 255 (accept_3_4 70 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 255 (accept_3_4 67 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 255 (Polychromatic418967fa.accept_30_6_17_15_1_15571 66 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 255 (accept_3_4 64 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 107
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 255 (accept_3_4 61 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 255 (accept_3_4 58 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 255 (accept_3_4 55 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 255 (accept_3_4 52 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 255 (accept_3_4 49 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 255 (accept_3_4 46 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 255 (accept_3_4 43 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 255 (accept_3_4 40 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 255 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 107 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 255 (accept_3_4 37 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 255 (accept_3_4 34 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 255 (accept_3_4 31 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 255 (Polychromatic418967fa.accept_19_11_12_8_1_11492 30 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 255 (accept_3_4 28 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 255 (accept_3_4 25 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 255 (accept_3_4 22 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 255 (accept_3_4 19 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 255 (accept_3_4 16 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 255 (accept_3_4 13 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 255 (accept_3_4 10 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 255 (accept_3_4 7 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 255 (accept_3_4 4 107 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 107 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 255 (accept_3_4 1 107 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 255 (allA_succ_of_accept 105 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 255 (accept_3_5 104 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 106
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 102 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 255 (accept_3_5 101 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 99 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 255 (accept_3_5 98 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 96 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 255 (accept_3_5 95 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 255 (accept_3_5 92 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 255 (accept_3_5 89 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 255 (accept_3_5 86 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 84 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 255 (accept_3_5 83 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 255 (accept_3_5 80 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 78 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 255 (accept_3_5 77 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 255 (accept_3_5 74 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 255 (accept_3_5 71 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 255 (Polychromatic418967fa.accept_20_10_6_15_1_5381 70 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 255 (accept_3_5 68 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 255 (accept_3_5 65 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 255 (Polychromatic418967fa.accept_30_3_16_15_1_13411 63 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 255 (accept_3_5 62 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 255 (accept_3_5 59 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 255 (accept_3_5 56 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 255 (accept_3_5 53 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 255 (Polychromatic418967fa.accept_20_12_6_15_1_6845 52 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 255 (accept_3_5 50 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 255
  (Polychromatic418967fa.accept_19_10_11_8_1_10121 48 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 106 255 (accept_3_5 47 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 106 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 106 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 255 (accept_3_5 44 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 255 (accept_3_5 41 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 255 (accept_3_5 38 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 255
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 255 (accept_3_5 35 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 255 (accept_3_5 32 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 255 (accept_3_5 29 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 255 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 255 (accept_3_5 26 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 255 (accept_3_5 23 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 255 (accept_3_5 20 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 255 (accept_3_5 17 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 255 (accept_3_5 14 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 255 (accept_3_5 11 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 255 (accept_3_5 8 106 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 255 (accept_3_5 5 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 255 (Polychromatic418967fa.accept_19_3_11_8_1_3193 3 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 255 (accept_3_5 2 106 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 255 (allA_succ_of_accept 104 105 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 105 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 103 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 255 3 34 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 101 105 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 255 5 20 21 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 105 255 3 33 35 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 105 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 97 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 105 255 3 32 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 105 255 5 19 21 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 105 255 3 31 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 105 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 92 105 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  91 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 255 15 6 7 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 89 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 88 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 255 3 29 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 255 5 17 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 105 255 3 28 35 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 255 3 27 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 105 255 5 16 21 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 255 3 26 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 105 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  76 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 255 15 5 7 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 255 3 24 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 255 5 14 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 105 255 3 23 35 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 255 3 22 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 105 255 5 13 21 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 255 3 21 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 255 15 4 7 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 255 3 19 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 255 5 11 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 105 255 3 18 35 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 255 3 17 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 105 255 5 10 21 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 255 3 16 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 105 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 255 15 3 7 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 255 3 14 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 255 5 8 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 105 255 3 13 35 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 255 3 12 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 255 5 7 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 255 3 11 35 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 255 15 2 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 255 3 9 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 255 5 5 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 105 255 3 8 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 255 3 7 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 105 255 5 4 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 105 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 255 3 6 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 255 15 1 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 255 3 4 35 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 255 5 2 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 255 3 3 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 105 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 255 3 2 35 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 255 5 1 21 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 255 3 1 35 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 255 (allA_succ_of_accept 103 104 255 (accept_3_4 103 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 101 104
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 255 (accept_3_4 100 104
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 99 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 98 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 255 (accept_3_4 97 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 95
  104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 255 (accept_3_4 94
  104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 255 (accept_3_4 91 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 104 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 89
  104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 104 255 (accept_3_4 88
  104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 104 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 255 (accept_3_4 85 104 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 104 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 84 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 255 (accept_3_4 82 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 80 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 255 (accept_3_4 79 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 255 (accept_3_4 76 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 255 (Polychromatic418967fa.accept_19_18_9_8_1_3267 75 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 255 (accept_3_4 73 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 255 (accept_3_4 70 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 68 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 255 (accept_3_4 67 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 104
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 255 (accept_3_4 64 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 255 (accept_3_4 61 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 255 (accept_3_4 58 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 255 (Polychromatic418967fa.accept_16_9_8_15_1_5095 57 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 255 (accept_3_4 55 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 255 (accept_3_4 52 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 255 (Polychromatic418967fa.accept_20_10_4_15_1_12657 50 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 255 (accept_3_4 49 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 255 (Polychromatic418967fa.accept_18_12_14_3_1_2655 48 104
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 255 (accept_3_4 46 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 255 (accept_3_4 43 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 255 (accept_3_4 40 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 255 (accept_3_4 37 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 255 (accept_3_4 34 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 255 (accept_3_4 31 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 255 (accept_3_4 28 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 27 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 255 (accept_3_4 25 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 255 (accept_3_4 22 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 255 (accept_3_4 19 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 255 (accept_3_4 16 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 255 (Polychromatic418967fa.accept_19_14_9_8_1_7271 14 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 255 (accept_3_4 13 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 255 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 104
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 255 (accept_3_4 10 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 255 (accept_3_4 7 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 104 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 255 (accept_3_4 4 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 255 (Polychromatic418967fa.accept_22_3_16_13_1_15541 3 104 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 255 (accept_3_4 1 104 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 255 (allA_succ_of_accept 102 103 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 102 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 255 (accept_3_5 101 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 255 (accept_3_5 98 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 97 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 96 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 255 (accept_3_5 95 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 255 (accept_3_5 92 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 255 (Polychromatic418967fa.accept_20_10_3_15_1_1546 90 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 255 (accept_3_5 89 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 255 (accept_3_5 86 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 255 (Polychromatic418967fa.accept_18_12_13_3_1_6427 84 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 255 (accept_3_5 83 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 255 (accept_3_5 80 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 255 (accept_3_5 77 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 255
  (Polychromatic418967fa.accept_11_9_4_2_1_600 75 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 255 (accept_3_5 74 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 255 (accept_3_5 71 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 255 (accept_3_5 68 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 255 (accept_3_5 65 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 255
  (Polychromatic418967fa.accept_18_9_13_3_1_5088 63 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 255 (accept_3_5 62 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 255 (accept_3_5 59 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 255 (accept_3_5 56 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 255 (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 255 (accept_3_5 53 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 255 (accept_3_5 50 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 255 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 255 (accept_3_5 47 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 255 (accept_3_5 44 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 255 (accept_3_5 41 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 255 (accept_3_5 38 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 255 (accept_3_5 35 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 255 (accept_3_5 32 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 255 (accept_3_5 29 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 255 (accept_3_5 26 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 255 (accept_3_5 23 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 255 (accept_3_5 20 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 255 (accept_3_5 17 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 255 (accept_3_5 14 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 255 (Polychromatic418967fa.accept_23_13_11_2_1_3894 13 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 255 (accept_3_5 11 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 255 (accept_3_5 8 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 255 (accept_3_5 5 103 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 255
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 255 (accept_3_5 2 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 255 (allA_succ_of_accept 101 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 102 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 100 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 102 255 3 33 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 102 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 98 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 255 3 32 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 255
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 95 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 94 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 102 255 3 31 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 102 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 92
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 255
  (Polychromatic418967fa.accept_14_7_4_3_1_488 91 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 255 3 30 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 255 (Polychromatic418967fa.accept_10_8_2_5_1_596
  88 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 102 255 3 29 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 102 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 102 255 17 5 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 102 255 3 28 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 255 (Polychromatic418967fa.accept_12_10_6_3_1_786
  82 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 102 255 3 27 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 102 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 79 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 255 3 26 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 76 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 102 255 3 25 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 102 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 74 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 102 255 3 24 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 102 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 102 255 3 23 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 255 17 4 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 255 (Polychromatic418967fa.accept_10_7_2_5_1_298
  67 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 102 255 3 22 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 102 255 3 21 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 102 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 62
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 255 3 20 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 255 (Polychromatic418967fa.accept_21_17_18_3_1_4909 59 102 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 58 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 102 255 3 19 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 102 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 102 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 255 3 18 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 255 (Polychromatic418967fa.accept_12_4_6_3_1_332
  52 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 255 51 1 2 5 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 255 3 16 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 255 (Polychromatic418967fa.accept_10_7_2_5_1_298
  47 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 255 3 15 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 255 3 14 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 255 3 13 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 255 (Polychromatic418967fa.accept_10_8_2_5_1_596
  38 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 255 3 12 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 102 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 255 17 2 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 255 3 11 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 255 (Polychromatic418967fa.accept_18_13_12_3_1_3857 31 102 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 255 3 10 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 102 255 3 9 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 102 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 255 3 8 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 102 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 255 3 7 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 255 3 6 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 102 255 17 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 102 255 (Polychromatic418967fa.accept_12_4_6_3_1_332
  16 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 255 3 5 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 255 3 4 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 255 (Polychromatic418967fa.accept_19_11_7_8_1_2110
  11 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 255 3 3 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 102 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 255 3 2 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 102 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 255 3 1 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 102 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 255 (allA_succ_of_accept 100 101 255 (accept_3_4 100 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 99 101 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 255 (accept_3_4 97 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771
  96 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 95 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 255 (accept_3_4 94 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 255 (accept_3_4 91 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 89 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 255 (accept_3_4 88 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 255 (accept_3_4 85 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 255
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 83 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 255 (accept_3_4 82 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 255 (accept_3_4 79 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 255 (accept_3_4 76 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 255 (Polychromatic418967fa.accept_21_12_17_3_1_11145 75 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 255 (accept_3_4 73 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 101
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 255 (accept_3_4 70 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 255 (accept_3_4 67 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 255
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 255 (accept_3_4 64 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 255 (accept_3_4 61 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 255 (accept_3_4 58 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 255 (accept_3_4 55 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 255 (accept_3_4 52 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 255 (accept_3_4 49 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 255 (Polychromatic418967fa.accept_28_20_17_3_1_15570 48 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 255
  (Polychromatic418967fa.accept_20_7_1_15_1_2700 47 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 255 (accept_3_4 46 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 255 (accept_3_4 43 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 255 (accept_3_4 40 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 255 (accept_3_4 37 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 255 (accept_3_4 34 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 255 (accept_3_4 31 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 255 (accept_3_4 28 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 255 (Polychromatic418967fa.accept_20_7_1_15_1_2700 27 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 255 (accept_3_4 25 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 255 (accept_3_4 22 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 255 (accept_3_4 19 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 255 (accept_3_4 16 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 255 (accept_3_4 13 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 255
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 255 (accept_3_4 10 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 101 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 255 (accept_3_4 7 101 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 255 (accept_3_4 4 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 255 (Polychromatic418967fa.accept_19_3_6_8_1_8819 3 101 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 255 (accept_3_4 1 101 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 255 (allA_succ_of_accept 99 100 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 100 255 (accept_3_5 98 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 100 255 5 19 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 100 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 255
  (Polychromatic418967fa.accept_21_9_16_3_1_11133 93 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 100 255 (accept_3_5 92 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 255 5 18 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 255 (accept_3_5 89 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 255 (accept_3_5 86 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  100 255 5 17 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 100 255 (Polychromatic418967fa.accept_23_15_8_2_1_15569 84 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 255 (accept_3_5 83 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 255
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 81 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 100 255 5 16 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 255 (Polychromatic418967fa.accept_7_1_2_3_1_257
  78 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 255 (accept_3_5 77
  100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 100 255 5 15 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 100 255 (accept_3_5 74 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 255 (Polychromatic418967fa.accept_13_7_9_8_1_188 72 100
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 255 (accept_3_5 71 100
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 255 5 14 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 255 (accept_3_5 68 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 100 255 5 13 20 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 100 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 100 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 255 (accept_3_5 62 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 255 5 12 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 255 (accept_3_5 59 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 100 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 255 (accept_3_5 56 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  100 255 5 11 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 100 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 255 (accept_3_5 53 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 100 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 255 (Polychromatic418967fa.accept_8_3_4_7_1_475
  51 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 255 5 10 20 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 100 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 255 (accept_3_5 47 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 100 255 (Polychromatic418967fa.accept_13_7_9_8_1_188 46 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 100 255 5 9 20 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 100 255 (accept_3_5 44 100 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 255 (accept_3_5 41 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  100 255 5 8 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 100 255 (Polychromatic418967fa.accept_21_18_16_3_1_8068 39 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 100 255 (accept_3_5 38 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 100 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 100 255 5 7 20 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 100 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 100 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 255 (accept_3_5 32 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 255 5 6 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 255 (accept_3_5 29 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 255 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 100
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 255 (accept_3_5 26 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  100 255 5 5 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 100 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 100 255 (accept_3_5 23 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 100 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 100
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 255 5 4 20 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 100 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 255 (accept_3_5 17 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 100 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 100 255 5 3 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 100 255 (accept_3_5 14 100 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 255 (accept_3_5 11 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 255 5 2 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 255 (Polychromatic418967fa.accept_21_9_16_3_1_11133 9 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 100 255 (accept_3_5 8 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 255 5 1 20 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 100 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 255 (accept_3_5 2 100 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_255_segment_000))))))))))))))))))))))))))))))))))))))))))


