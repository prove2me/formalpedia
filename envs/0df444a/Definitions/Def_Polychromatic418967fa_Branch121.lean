-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch121
-- name    : Polychromatic418967fa_Branch121
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:44.938788+00:00
-- url     : https://prove2.me/theorems/0e8555aa-1f06-4626-ba69-8495a94afd63
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_121 : allB 121 121 :=
  allB_succ' 2 120 121 (Eq.refl Bool.true) (allA_succ_of_accept 1 120 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  120 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 121)) (allB_succ' 3 119 121
  (Eq.refl Bool.true) (allA_of_3_1 3 119 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 118 121 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 121 (accept_3_3 2 118 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 118 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 121)))) (allB_succ' 5 117 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 117 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 121 (accept_3_3 2 117 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 121 (Polychromatic418967fa.accept_16_1_5_9_1_1649
  1 117 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 121))))) (allB_succ' 6 116 121
  (Eq.refl Bool.true) (allA_of_3_1 6 116 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 115 121 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 115 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 121 (accept_3_3 5 115 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 121 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 115 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 121 (accept_3_3 2 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 121))))))) (allB_succ' 8 114 121 (Eq.refl Bool.true) (allA_succ_of_accept 7 114 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 114 121 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 114 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 121 (accept_3_3 5 114 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 114 121 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 114 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  114 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 121 (accept_3_3 2 114
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 121 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 114 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 121)))))))) (allB_succ' 9 113 121
  (Eq.refl Bool.true) (allA_of_3_1 9 113 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 112 121 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 121 (accept_3_3 8 112 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 121 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 112 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 121
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 121 (accept_3_3 5 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 121 (Polychromatic418967fa.accept_21_4_7_16_1_2938 4 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 121 (accept_3_3 2 112 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 121 (Polychromatic418967fa.accept_21_1_7_16_1_5859 1 112 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 121)))))))))) (allB_succ' 11 111 121 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 111 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 121 (accept_3_3 8 111
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 121
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 121 (accept_3_3 5 111 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 121 (accept_3_3 2 111
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 121 (Polychromatic418967fa.accept_7_1_6_2_1_18
  1 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 121))))))))))) (allB_succ' 12 110
  121 (Eq.refl Bool.true) (allA_of_3_1 12 110 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 109 121
  (Eq.refl Bool.true) (allA_succ_of_accept 12 109 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 121 (accept_3_3 11 109 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 121 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 109
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 121
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 121 (accept_3_3 8 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 109 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 121 (accept_3_3 5 109 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 109 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 121 (accept_3_3 2 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 121 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 121))))))))))))) (allB_succ' 14 108 121 (Eq.refl Bool.true) (allA_succ_of_accept 13 108 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 108 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 121 (accept_3_3 11 108 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 108 121 (Polychromatic418967fa.accept_21_10_3_16_1_5909 10 108 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 121
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 121 (accept_3_3 8 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 121 (Polychromatic418967fa.accept_20_7_8_1_1_5856 7 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 121 (accept_3_3 5 108 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 121 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 108 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 121
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 121 (accept_3_3 2 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 121)))))))))))))) (allB_succ' 15 107 121 (Eq.refl Bool.true) (allA_of_3_1 15 107 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 106 121 (Eq.refl Bool.true) (allA_succ_of_accept 15 106 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 121 (accept_3_3 14 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 106 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 121 (accept_3_3 11 106 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 106 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 121 (accept_3_3 8 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 106 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 121 (accept_3_3 5 106 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 106 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 121 (accept_3_3 2 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 121)))))))))))))))) (allB_succ' 17 105 121 (Eq.refl Bool.true) (allA_succ_of_accept 16 105
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 105 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 121 (accept_3_3 14 105 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 121 (Polychromatic418967fa.accept_22_13_17_11_1_5908 13 105 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 121 (accept_3_3 11 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 121 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 121 (accept_3_3 8 105 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 121
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 121 (accept_3_3 5 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 121 (accept_3_3 2 105 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 121))))))))))))))))) (allB_succ' 18 104 121 (Eq.refl
  Bool.true) (allA_of_3_1 18 104 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 103 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 103 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 121 (accept_3_3 17 103 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 103 121 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 103 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 121
  (Polychromatic418967fa.accept_13_2_12_4_1_943 15 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 121 (accept_3_3 14 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 121 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 121 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 103 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 121 (accept_3_3 11 103 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 121
  (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 121 (accept_3_3 8 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 121 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 121 (accept_3_3 5 103 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 121 (accept_3_3 2 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 121 (Polychromatic418967fa.accept_19_1_8_7_1_4470 1 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 121))))))))))))))))))) (allB_succ' 20 102 121 (Eq.refl Bool.true) (allA_succ_of_accept 19
  102 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 102 121 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 102 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 121 (accept_3_3 17 102 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 102 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 121 (accept_3_3 14 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 102 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 102 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 121 (accept_3_3 11 102 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 102 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 121
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 102 121 (accept_3_3 8 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  102 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 102 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 121 (accept_3_3 5 102 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 121 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 102 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 102 121 (accept_3_3 2 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  102 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 102 121)))))))))))))))))))) (allB_succ' 21 101 121 (Eq.refl Bool.true) (allA_of_3_1 21 101 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 100 121 (Eq.refl Bool.true) (allA_succ_of_accept 21 100 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 121 (accept_3_3 20 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 121 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 121 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 100 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 121 (accept_3_3 17 100 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 121 (accept_3_3 14 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 121 (accept_3_3 11 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 100 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 121 (accept_3_3 8 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 121 (accept_3_3 5 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 121 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 100 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 121 (accept_3_3 2 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 121 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 121)))))))))))))))))))))) (allB_succ' 23 99 121 (Eq.refl Bool.true) (allA_succ_of_gcd 22 99
  121 11 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  99 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 121 (accept_3_3 20 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 121 (Polychromatic418967fa.accept_24_19_3_1_1_5907 19 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 121 (accept_3_3 17 99 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 121
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 121 (accept_3_3 14 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 121 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 99 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 121 11 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 121 (accept_3_3 8 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  121 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 121 (accept_3_3 5 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 121 (accept_3_3 2 99 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 121 (Polychromatic418967fa.accept_19_1_4_7_1_2018 1
  99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 121)))))))))))))))))))))))
  (allB_succ' 24 98 121 (Eq.refl Bool.true) (allA_of_3_1 24 98 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  25 97 121 (Eq.refl Bool.true) (allA_succ_of_accept 24 97 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 121 (accept_3_3 23 97 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 22
  97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 121 (accept_3_3 20 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 121 (accept_3_3 17 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 121 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 97 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 121 (accept_3_3 14 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 121 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 121 (accept_3_3 11 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 97 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 121
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 121 (accept_3_3 8 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  121 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 121 (accept_3_3 5 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 97
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 121 (accept_3_3 2 97 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 121))))))))))))))))))))))))) (allB_succ'
  26 96 121 (Eq.refl Bool.true) (allA_succ_of_accept 25 96 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 121 (accept_3_3 23 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 121 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 121 (accept_3_3 20 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 121 (accept_3_3 17 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 121 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 121 (accept_3_3 14 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 121 (Polychromatic418967fa.accept_19_13_1_7_1_5906 13 96 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 121 (accept_3_3 11 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 121 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 121 (accept_3_3 8 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 121
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 121 (accept_3_3 5 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 121 (accept_3_3 2 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 121)))))))))))))))))))))))))) (allB_succ' 27 95 121 (Eq.refl
  Bool.true) (allA_of_3_1 27 95 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 94 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 94 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 121 (accept_3_3 26 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 94 121 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 121 (Polychromatic418967fa.accept_17_7_9_2_1_629
  24 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 121 (accept_3_3 23
  94 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 121
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 94 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 121 (accept_3_3 20 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 94 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 121 (Polychromatic418967fa.accept_15_3_4_1_1_1072
  18 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 121 (accept_3_3 17
  94 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 121
  (Polychromatic418967fa.accept_12_4_10_1_1_706 16 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 94 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 121 (accept_3_3 14 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 94 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 121 (accept_3_3 11 94
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 121
  (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 94 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 121 (accept_3_3 8 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 94 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 121 (accept_3_3 5 94 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4
  94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 121 (accept_3_3 2 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 121)))))))))))))))))))))))))))) (allB_succ' 29 93 121 (Eq.refl Bool.true) (allA_succ_of_accept 28 93 121
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 93 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 121 (accept_3_3 26 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 93 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 24
  93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 121 (accept_3_3 23 93
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 121 (Polychromatic418967fa.accept_6_4_3_1_1_57
  22 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 121
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 121 (accept_3_3 20 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 121 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 121 (accept_3_3 17 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 121 (accept_3_3 14 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 121 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 121 (accept_3_3 11 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 121
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 9 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 121 (accept_3_3 8 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 121 (accept_3_3 5 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 121 (accept_3_3 2 93 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 93
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 121)))))))))))))))))))))))))))))
  (allB_succ' 30 92 121 (Eq.refl Bool.true) (allA_of_3_1 30 92 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  31 91 121 (Eq.refl Bool.true) (allA_succ_of_accept 30 91 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 121 (accept_3_3 29 91 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 121
  (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 91 121 (Polychromatic418967fa.accept_19_8_15_7_1_323 27 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 121 (accept_3_3 26 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 91 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 121 (accept_3_3 23 91
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 121 (Polychromatic418967fa.accept_4_2_3_1_1_2
  22 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 121 (accept_3_3 20 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 121 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 121 (accept_3_3 17 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 121 (accept_3_3 14 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 121 (Polychromatic418967fa.accept_17_13_6_2_1_5850 13 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 121 (accept_3_3 11 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 121
  (Polychromatic418967fa.accept_21_9_7_16_1_5904 9 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 121 (accept_3_3 8 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 121 (accept_3_3 5 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 121 (Polychromatic418967fa.accept_16_4_11_9_1_1631 4 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 121 (accept_3_3 2 91 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 121 (Polychromatic418967fa.accept_17_1_6_2_1_623 1
  91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 121)))))))))))))))))))))))))))))))
  (allB_succ' 32 90 121 (Eq.refl Bool.true) (allA_succ_of_accept 31 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 121
  (Polychromatic418967fa.accept_19_11_14_7_1_4473 30 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 121 (accept_3_3 29 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 121 (Polychromatic418967fa.accept_13_2_12_4_1_943 28 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 121 (accept_3_3 26 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 90 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 121 (accept_3_3 23 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 121 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 90 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 121 (accept_3_3 20 90 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 121 (accept_3_3 17 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 121 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 121 (accept_3_3 14 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 121 (Polychromatic418967fa.accept_20_13_10_1_1_5903 13 90 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 121
  (Polychromatic418967fa.accept_19_12_14_7_1_5865 12 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 121 (accept_3_3 11 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 121 (Polychromatic418967fa.accept_20_9_10_1_1_192 9 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 121 (accept_3_3 8 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 121
  (Polychromatic418967fa.accept_19_6_14_7_1_5902 6 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 121 (accept_3_3 5 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 121 (accept_3_3 2 90 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 121)))))))))))))))))))))))))))))))) (allB_succ' 33 89 121
  (Eq.refl Bool.true) (allA_of_3_1 33 89 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 88 121 (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 88 121 11 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 88 121 (accept_3_3 32 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 88 121 (Polychromatic418967fa.accept_13_5_10_4_1_1564 31 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 88 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 121 (accept_3_3 29 88 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 121 (accept_3_3 26 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 121 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 121 (accept_3_3 23 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 121 11 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 88 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 121 (accept_3_3 20 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 121
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 121 (accept_3_3 17 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 121 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 121 (accept_3_3 14 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 88 121 11 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 88 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 121 (accept_3_3 8 88 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 121 (Polychromatic418967fa.accept_13_7_10_4_1_919 7
  88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 121 (accept_3_3 5 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  121 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 121 (accept_3_3 2 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 121)))))))))))))))))))))))))))))))))) (allB_succ' 35
  87 121 (Eq.refl Bool.true) (allA_succ_of_accept 34 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 121
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 121 (accept_3_3 32 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 121 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 121 (accept_3_3 29 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 121 (accept_3_3 26 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 121 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 121 (accept_3_3 23 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 121 (accept_3_3 20 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 121 (accept_3_3 17 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 121
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 121 (accept_3_3 14 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 121 (accept_3_3 11 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 121 (accept_3_3 8 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 121 (accept_3_3 5 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 121 (accept_3_3 2 87 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 87
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 121)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 86 121 (Eq.refl Bool.true) (allA_of_3_1 36 86 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 85 121 (Eq.refl Bool.true) (allA_succ_of_accept 36 85 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 121 (accept_3_3 35 85 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 34
  85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 121
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 121 (accept_3_3 32 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 121 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 121 (accept_3_3 29 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 85 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 121 (accept_3_3 26 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 121 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 121 (accept_3_3 23 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 121 (Polychromatic418967fa.accept_13_9_7_4_1_953 22 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 121
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 121 (accept_3_3 20 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 121 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 121 (Polychromatic418967fa.accept_27_18_4_13_1_5900 18 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 121 (accept_3_3 17 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 121 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 85 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 121
  (Polychromatic418967fa.accept_20_15_5_1_1_5899 15 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 121 (accept_3_3 14 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 121 (accept_3_3 11 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 121 (accept_3_3 8 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  121 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 121 (accept_3_3 5 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 85 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 121
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 121 (accept_3_3 2 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  121 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 121))))))))))))))))))))))))))))))))))))) (allB_succ' 38 84 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 121 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 84
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 121 (accept_3_3 35 84 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 34
  84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 121 (accept_3_3 32 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  84 121 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 121 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 121 (accept_3_3 29 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 121
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 121 (accept_3_3 26 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 121 (accept_3_3 23 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 121 (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 121
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 121 (accept_3_3 20 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  84 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 121 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 121 (accept_3_3 17 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 121 (accept_3_3 14 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  84 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 121 (Polychromatic418967fa.accept_16_12_4_9_1_4633 12 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 121 (accept_3_3 11 84 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 121
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 121 (accept_3_3 8 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84
  121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 84 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 121 (accept_3_3 5 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 84 121 (Polychromatic418967fa.accept_22_4_18_11_1_5898 4 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 121 (Polychromatic418967fa.accept_18_3_12_13_1_3307
  3 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 121 (accept_3_3 2 84
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 121 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  121)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 83 121 (Eq.refl Bool.true) (allA_of_3_1 39 83 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 82 121 (Eq.refl Bool.true) (allA_succ_of_accept 39 82 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 121 (accept_3_3 38 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 121 (Polychromatic418967fa.accept_17_3_14_2_1_646 37 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 121 (accept_3_3 35 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 121 (accept_3_3 32 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 121 (accept_3_3 29 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 121 (accept_3_3 26 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 121 (accept_3_3 23 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 121 (Polychromatic418967fa.accept_16_6_2_9_1_5897 22 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 121 (accept_3_3 20 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 121 (accept_3_3 17 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 121 (accept_3_3 14 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 121 (accept_3_3 11 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 121 (accept_3_3 8 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 121 (accept_3_3 5 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 121 (accept_3_3 2 82 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 121 (Polychromatic418967fa.accept_16_1_2_9_1_1607 1
  82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  121)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 81 121 (Eq.refl Bool.true) (allA_succ_of_accept 40 81 121
  (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 81 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 121 (accept_3_3 38 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 81 121 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 121 (Polychromatic418967fa.accept_19_17_5_7_1_5896
  36 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 121 (accept_3_3 35
  81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 121
  (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 81 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 121 (accept_3_3 32 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 81 121 (Polychromatic418967fa.accept_19_12_5_7_1_5895 31 81 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 121
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 121 (accept_3_3 29 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 121 (accept_3_3 26 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 121 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 81 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 121
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 121 (accept_3_3 23 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 121 (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 121 (accept_3_3 20 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 81 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 121
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 121 (accept_3_3 17 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 121 (accept_3_3 14 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 121 (accept_3_3 11 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 121 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 121 (accept_3_3 8 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 121 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 81 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 121 (accept_3_3 5 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 121 (accept_3_3 2 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 121 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 121))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 80
  121 (Eq.refl Bool.true) (allA_of_3_1 42 80 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 79 121 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 121 (accept_3_3 41 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 121 (Polychromatic418967fa.accept_16_8_15_9_1_4676 40 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 121 (accept_3_3 38 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 121 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 121 (accept_3_3 35 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 121 (accept_3_3 32 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 121 (Polychromatic418967fa.accept_13_5_1_4_1_3966 31 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 121 (accept_3_3 29 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 121
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 121 (accept_3_3 26 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 121 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 121 (accept_3_3 23 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 121 (accept_3_3 20 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 121 (accept_3_3 17 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 121 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 121 (accept_3_3 14 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 121 (Polychromatic418967fa.accept_19_13_3_7_1_4423 13 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 121 (accept_3_3 11 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 121
  (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 121 (accept_3_3 8 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  121 (Polychromatic418967fa.accept_25_7_4_21_1_5893 7 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 121 (accept_3_3 5 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 121 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 121 (accept_3_3 2 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 121))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 78 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 121 (Polychromatic418967fa.accept_17_8_10_2_1_4546 42 78
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 121 (accept_3_3 41 78 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 121
  (Polychromatic418967fa.accept_22_18_12_11_1_5892 40 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 121 (accept_3_3 38 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 121
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 121 (accept_3_3 35 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 121 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 121 (accept_3_3 32 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 121 (accept_3_3 29 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 121 (accept_3_3 26 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 121
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 121 (accept_3_3 23 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 121 (Polychromatic418967fa.accept_21_1_15_16_1_5891 22 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 121 (accept_3_3 20 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 121
  (Polychromatic418967fa.accept_21_18_15_16_1_2917 18 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 121 (accept_3_3 17 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 121 (accept_3_3 14 78 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 121 (accept_3_3 11 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 121 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 121 (accept_3_3 8 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 121 (accept_3_3 5 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  121 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 121 (accept_3_3 2 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 121)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  77 121 (Eq.refl Bool.true) (allA_of_3_1 45 77 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 76 121
  (Eq.refl Bool.true) (allA_succ_of_accept 45 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 121 (accept_3_3 44 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 76 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 121
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 121 (accept_3_3 41 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 121 (Polychromatic418967fa.accept_16_8_12_9_1_2569 40 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 121 (accept_3_3 38 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 121 (accept_3_3 35 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 121 (accept_3_3 32 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 121
  (Polychromatic418967fa.accept_21_9_13_16_1_2914 30 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 121 (accept_3_3 29 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 121 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 121 (accept_3_3 26 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 121 (accept_3_3 23 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 121 (accept_3_3 20 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 121 (Polychromatic418967fa.accept_13_6_11_4_1_938 19 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 121 (accept_3_3 17 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 121 (Polychromatic418967fa.accept_17_16_8_2_1_5890 16 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 121 (accept_3_3 14 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 121
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 121 (accept_3_3 11 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 121 (accept_3_3 8 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 121 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 121
  (Polychromatic418967fa.accept_13_6_11_4_1_938 6 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 121 (accept_3_3 5 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 121 (accept_3_3 2 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 121)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47
  75 121 (Eq.refl Bool.true) (allA_succ_of_accept 46 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 121 (accept_3_3 44 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 121 (accept_3_3 41 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 121 (accept_3_3 38 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 121 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 121 (accept_3_3 35 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 121 (accept_3_3 32 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 121 (accept_3_3 29 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 121
  (Polychromatic418967fa.accept_13_1_10_4_1_954 27 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 121 (accept_3_3 26 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 121 (accept_3_3 23 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 121 (accept_3_3 20 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 121 (accept_3_3 17 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 121 (accept_3_3 14 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 121 (Polychromatic418967fa.accept_17_13_7_2_1_4562 13 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 121 (Polychromatic418967fa.accept_17_12_7_2_1_4561 12 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 121 (accept_3_3 11 75 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 121 (accept_3_3 8 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 121 (accept_3_3 5 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 121 (accept_3_3 2 75 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 75
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  121))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 74 121 (Eq.refl Bool.true) (allA_of_3_1 48 74 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 73 121 (Eq.refl Bool.true) (allA_succ_of_accept 48 73 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 121 (accept_3_3 47 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 121 (Polychromatic418967fa.accept_18_10_1_13_1_2192 46 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 121 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 121 (accept_3_3 44 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 73 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 121 (accept_3_3 41 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 121 (accept_3_3 38 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 121 (Polychromatic418967fa.accept_13_11_8_4_1_3950 37 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 121
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 121 (accept_3_3 35 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 121 (accept_3_3 32 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 121 (Polychromatic418967fa.accept_17_14_5_2_1_4559 31 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 121 (accept_3_3 29 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 121 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 121 (accept_3_3 26 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 121 (accept_3_3 23 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 121 (accept_3_3 20 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 121
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 121 (accept_3_3 17 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 121 (accept_3_3 14 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 121
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 121 (accept_3_3 11 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 121 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 121 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 121 (accept_3_3 8 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 121 (accept_3_3 5 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  121 (Polychromatic418967fa.accept_19_4_16_7_1_5870 4 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 121 (accept_3_3 2 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 121)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 72 121 (Eq.refl Bool.true) (allA_succ_of_accept 49 72 121 (Polychromatic418967fa.accept_10_9_2_1_1_840
  49 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 121
  (Polychromatic418967fa.accept_13_9_7_4_1_953 48 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 121 (accept_3_3 47 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 121 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 121 (accept_3_3 44 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 121
  (Polychromatic418967fa.accept_13_3_7_4_1_435 42 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 121 (accept_3_3 41 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 121 (Polychromatic418967fa.accept_17_6_4_2_1_5889 40 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 121 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 121 (accept_3_3 38 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 121 (Polychromatic418967fa.accept_13_11_7_4_1_1561 37 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 121
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 121 (accept_3_3 35 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 121 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 121 (accept_3_3 32 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 121 (Polychromatic418967fa.accept_16_15_8_9_1_2563 31 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 121
  (Polychromatic418967fa.accept_19_11_15_7_1_3177 30 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 121 (accept_3_3 29 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 121 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 121 (Polychromatic418967fa.accept_19_8_15_7_1_323 27 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 121 (accept_3_3 26 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 121 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 121
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 121 (accept_3_3 23 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 121 (Polychromatic418967fa.accept_13_9_7_4_1_953 22 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 121 (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 121 (accept_3_3 20 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 121 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 121
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 121 (accept_3_3 17 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 121 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 121 (accept_3_3 14 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 121
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 121 (accept_3_3 11 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 121 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 121 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 121 (accept_3_3 8 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 121 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 121
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 121 (accept_3_3 5 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  121 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 121 (accept_3_3 2 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 121 (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 72 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 121))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 71 121 (Eq.refl Bool.true) (allA_of_3_1 51 71 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 70 121 (Eq.refl Bool.true) (allA_succ_of_accept 51 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 121 (accept_3_3 50 70 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 121 (Polychromatic418967fa.accept_13_10_5_4_1_3107
  49 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 121 (accept_3_3 47 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 121 (accept_3_3 44 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 121 (accept_3_3 41 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 121 (accept_3_3 38 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 121
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 121 (accept_3_3 35 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 121 (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 121 (accept_3_3 32 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 121 (accept_3_3 29 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 121 (accept_3_3 26 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 121 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 121 (accept_3_3 23 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 121 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 121 (accept_3_3 20 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 121
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 121 (accept_3_3 17 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 121 (accept_3_3 14 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 121 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 121 (accept_3_3 11 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 121 (accept_3_3 8 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 121 (accept_3_3 5 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 121 (accept_3_3 2 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  121)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 69 121 (Eq.refl Bool.true) (allA_succ_of_accept
  52 69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 121 (accept_3_3 50 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 121 (Polychromatic418967fa.accept_16_1_5_9_1_1649 49 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 121 (accept_3_3 47 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 121 (accept_3_3 44 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 121
  (Polychromatic418967fa.accept_10_2_9_1_1_185 42 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 121 (accept_3_3 41 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 121 (accept_3_3 38 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 121 (accept_3_3 35 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 121 (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 121 (accept_3_3 32 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 121 (accept_3_3 29 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 121 (accept_3_3 26 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 121 (accept_3_3 23 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 121 (accept_3_3 20 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 121 (accept_3_3 17 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 121 (accept_3_3 14 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 121 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 121
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 121 (accept_3_3 11 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 121 (Polychromatic418967fa.accept_21_9_6_16_1_5857 9 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 121 (accept_3_3 8 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 121
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 121 (accept_3_3 5 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 121 (accept_3_3 2 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 121)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 68 121 (Eq.refl Bool.true) (allA_of_3_1 54 68 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  55 67 121 (Eq.refl Bool.true) (allA_succ_of_accept 54 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 121 (accept_3_3 53 67 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 121 (Polychromatic418967fa.accept_17_1_16_2_1_1404
  52 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 121
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 51 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 121 (accept_3_3 50 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 121 (Polychromatic418967fa.accept_21_7_4_16_1_5888 49 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 121 (accept_3_3 47 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 121
  (Polychromatic418967fa.accept_13_6_2_4_1_923 45 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 121 (accept_3_3 44 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 121 (Polychromatic418967fa.accept_19_5_10_7_1_5887 43 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 121 (accept_3_3 41 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 121
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 121 (accept_3_3 38 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 121 (Polychromatic418967fa.accept_13_11_2_4_1_1590 37 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 121 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 121 (accept_3_3 35 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 121 (accept_3_3 32 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 121 (Polychromatic418967fa.accept_13_5_2_4_1_3955 31 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 121 (accept_3_3 29 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 121 (Polychromatic418967fa.accept_16_12_3_9_1_5886 28 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 121 (accept_3_3 26 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 121 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 121 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 121 (accept_3_3 23 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 121
  (Polychromatic418967fa.accept_15_6_7_1_1_93 21 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 121 (accept_3_3 20 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 121 (accept_3_3 17 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 121 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 121
  (Polychromatic418967fa.accept_20_15_7_1_1_5885 15 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 121 (accept_3_3 14 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 121 (accept_3_3 11 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 121
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 121 (accept_3_3 8 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  121 (Polychromatic418967fa.accept_16_7_3_9_1_2557 7 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 121 (accept_3_3 5 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 121 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 67 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 121
  (Polychromatic418967fa.accept_19_3_10_7_1_5884 3 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 121 (accept_3_3 2 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  121 (Polychromatic418967fa.accept_17_1_16_2_1_1404 1 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 67 121))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 66 121 (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 66 121 11 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 66 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 121 (accept_3_3 53 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 121 (accept_3_3 50 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 121 (Polychromatic418967fa.accept_13_10_1_4_1_3103 49 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 121 (accept_3_3 47 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 121
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 121 11 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 121 (accept_3_3 41 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 40
  66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 121 (accept_3_3 38 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 121 (accept_3_3 35 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 121 11 3 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 121 (accept_3_3 32 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 121
  (Polychromatic418967fa.accept_17_13_15_2_1_654 30 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 121 (accept_3_3 29 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 121 (accept_3_3 26 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 121 (accept_3_3 23 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66
  121 11 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  66 121 (Polychromatic418967fa.accept_17_4_15_2_1_4551 21 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 121 (accept_3_3 20 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 121 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 121 (accept_3_3 17 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 121 (accept_3_3 14 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 66 121 11 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 66 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 10
  66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 121
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 121 (accept_3_3 8 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 121 (accept_3_3 5 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 121 (Polychromatic418967fa.accept_17_4_15_2_1_4551 4 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 121 (accept_3_3 2 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  121)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 65 121 (Eq.refl Bool.true) (allA_of_3_1 57
  65 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 64 121 (Eq.refl Bool.true) (allA_succ_of_accept 57 64
  121 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 121 (accept_3_3 56 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 121 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 121 (accept_3_3 53 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 121 (accept_3_3 50 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 121 (Polychromatic418967fa.accept_17_15_13_2_1_3418 49 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 121 (accept_3_3 47 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 121 (accept_3_3 44 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 121 (accept_3_3 41 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 121 (Polychromatic418967fa.accept_17_6_13_2_1_4549 40 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 121 (accept_3_3 38 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 121 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 121 (Polychromatic418967fa.accept_21_15_1_16_1_2930 36 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 121 (accept_3_3 35 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 64 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 121 (accept_3_3 32 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 121 (accept_3_3 29 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 121 (Polychromatic418967fa.accept_13_2_12_4_1_943 28 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 121 (accept_3_3 26 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 121 (accept_3_3 23 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 121 (accept_3_3 20 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 121 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 121 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 121 (accept_3_3 17 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 121 (accept_3_3 14 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 121 (accept_3_3 11 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 121 (accept_3_3 8 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 121 (accept_3_3 5 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 121 (Polychromatic418967fa.accept_18_4_10_13_1_5883 4 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 121 (accept_3_3 2 64 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 121 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1
  64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 63 121 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 63 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 63 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 121 (accept_3_3 56 63 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 121 (Polychromatic418967fa.accept_17_4_12_2_1_2349
  55 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 121 (accept_3_3 53 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 121 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 121 (accept_3_3 50 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 121 (Polychromatic418967fa.accept_13_10_11_4_1_2248 49 63
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 121
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 121 (accept_3_3 47 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 121 (accept_3_3 44 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 121 (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 121 (accept_3_3 41 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 121 (Polychromatic418967fa.accept_18_3_9_13_1_1235 39 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 121 (accept_3_3 38 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 121 (Polychromatic418967fa.accept_19_18_6_7_1_5882 37 63
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 121
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 121 (accept_3_3 35 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  63 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 121 (accept_3_3 32 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 121 (Polychromatic418967fa.accept_22_9_19_11_1_5881 31 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 121 (accept_3_3 29 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 121 (Polychromatic418967fa.accept_17_10_12_2_1_3385 27 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 121 (accept_3_3 26 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 121 (Polychromatic418967fa.accept_13_12_11_4_1_3111 25 63
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 121
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 121 (accept_3_3 23 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 121 (accept_3_3 20 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 121 (Polychromatic418967fa.accept_13_6_11_4_1_938 19 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 121 (accept_3_3 17 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 121 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 121 (accept_3_3 14 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 121 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 121
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 121 (accept_3_3 11 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 121 (accept_3_3 8 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 121 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 63 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 121 (accept_3_3 5 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 121 (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 121 (accept_3_3 2 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 121 (Polychromatic418967fa.accept_19_1_6_7_1_2019 1 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 62 121 (Eq.refl Bool.true) (allA_of_3_1 60 62 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  61 121 (allA_succ_of_accept 60 61 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 121 (accept_3_3 59 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 61 121 (Polychromatic418967fa.accept_13_6_9_4_1_2288 58 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 61 121 (accept_3_3 56 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  61 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 61 121 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 61 121 (accept_3_3 53 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 61 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 61 121 (accept_3_3 50 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  61 121 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 61 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 121 (accept_3_3 47 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 61 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 61 121 (accept_3_3 44 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  61 121 (Polychromatic418967fa.accept_21_1_19_16_1_2901 43 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 61 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 121 (accept_3_3 41 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 121 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 121 (accept_3_3 38 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 121 (accept_3_3 35 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 121 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 121 (accept_3_3 32 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 121 (accept_3_3 29 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 121
  (Polychromatic418967fa.accept_22_5_17_11_1_5880 27 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 121 (accept_3_3 26 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 121 (accept_3_3 23 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 121 (Polychromatic418967fa.accept_16_6_13_9_1_4690 22 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 121 (accept_3_3 20 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 121 (accept_3_3 17 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 121 (Polychromatic418967fa.accept_19_16_4_7_1_5879 16 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 121 (accept_3_3 14 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 121 (Polychromatic418967fa.accept_19_13_4_7_1_5878 13 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 121 (accept_3_3 11 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 121
  (Polychromatic418967fa.accept_22_9_17_11_1_5877 9 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 121 (accept_3_3 8 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  121 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 61 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 121 (accept_3_3 5 61 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 121 (accept_3_3 2 61 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  121))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 121 (allA_succ_of_accept 59 60 121
  (accept_3_3 59 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 121
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 121 (accept_3_3 56 60 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 54
  60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 121 (accept_3_3 53 60
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 121
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 121 (Polychromatic418967fa.accept_13_12_8_4_1_3099 51 60 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 121 (accept_3_3 50 60 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 60 121 (Polychromatic418967fa.accept_13_10_8_4_1_3098 49 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 121 (accept_3_3 47 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 121 (accept_3_3 44 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 121
  (Polychromatic418967fa.accept_19_4_3_7_1_5876 42 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 121 (accept_3_3 41 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 121 (accept_3_3 38 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 121
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 121 (accept_3_3 35 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 121 (accept_3_3 32 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 121 (Polychromatic418967fa.accept_19_12_3_7_1_5832 31 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 121 (accept_3_3 29 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 121 (accept_3_3 26 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 121
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 121 (accept_3_3 23 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 121 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 121 (accept_3_3 20 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 121
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 121 (accept_3_3 17 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 121 (Polychromatic418967fa.accept_19_15_3_7_1_5875 15 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 121 (accept_3_3 14 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 121 (accept_3_3 11 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 121 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 121 (accept_3_3 8 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 121 (accept_3_3 5 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  121 (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 60 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 121 (accept_3_3 2 60 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 121 (allA_of_3_1 59 59 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 121 (allA_succ_of_accept 57 58 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 121 (accept_3_3 56 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 121 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 121 (accept_3_3 53 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 121 (accept_3_3 50 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 121 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 121 (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 121 (accept_3_3 47 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 121 (Polychromatic418967fa.accept_13_7_6_4_1_933 46 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 121 (accept_3_3 44 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 121 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 121 (accept_3_3 41 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 121 (accept_3_3 38 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 121 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 121 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 121 (accept_3_3 35 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 121 (Polychromatic418967fa.accept_22_12_14_11_1_5874 34 58
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 121 (accept_3_3 32 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 121 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 121 (accept_3_3 29 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 121 (accept_3_3 26 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 121 (Polychromatic418967fa.accept_14_11_2_9_1_5873 25 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 121 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 121 (accept_3_3 23 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 121 (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 58 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 121 (accept_3_3 20 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 121 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 121 (accept_3_3 17 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 121 (accept_3_3 14 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 121 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 121 (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 121 (accept_3_3 11 58 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 121 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 58
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 121 (accept_3_3 8 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 121 (Polychromatic418967fa.accept_19_6_1_7_1_5872 6 58 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 121 (accept_3_3 5 58 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 121 (accept_3_3 2 58 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 121 (Polychromatic418967fa.accept_16_1_10_9_1_4645
  1 58 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 121 (allA_succ_of_accept 56 57 121
  (accept_3_3 56 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 121 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 121 (accept_3_3 53 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 121 (accept_3_3 50 57
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 121
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 49 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 121 (accept_3_3 47 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 45
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 121 (accept_3_3 44 57
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 121
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 121 (accept_3_3 41 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 121 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 121 (accept_3_3 38
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 121
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 121 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 121 (accept_3_3 35 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 121 (accept_3_3 32 57
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 121
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 121 (Polychromatic418967fa.accept_17_13_6_2_1_5850 30 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 121 (accept_3_3 29 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 121 (accept_3_3 26 57
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 121
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 121 (accept_3_3 23 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 121 (Polychromatic418967fa.accept_17_4_6_2_1_5871
  21 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 121 (accept_3_3 20
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 121
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 121 (Polychromatic418967fa.accept_17_1_6_2_1_623 18 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 121 (accept_3_3 17 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 121 (accept_3_3 14 57
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 121 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 121 (accept_3_3 11 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 121 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 121 (accept_3_3 8 57 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 121 (accept_3_3 5 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 121 (accept_3_3 2 57 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 121 (allA_of_3_1 56 56 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 121
  (allA_succ_of_accept 54 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 121 (accept_3_3 53 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 51
  55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 121 (accept_3_3 50 55
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 121 (accept_3_3 47 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 55 121 11 4 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 121 (accept_3_3 41 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 121 (Polychromatic418967fa.accept_13_1_3_4_1_925 40 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 121 (accept_3_3 38 55
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 121
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 55 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 121 (accept_3_3 35 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 55 121 11 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 121 (accept_3_3 32 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 121 (accept_3_3 29 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 121 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 121 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 121 (accept_3_3 26 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 55 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 121 (accept_3_3 23 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55
  121 11 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  55 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 55 121 (accept_3_3 20 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 55 121 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 121 (accept_3_3 17 55 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16
  55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 121 (accept_3_3 14 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 121 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 55 121 11 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 121 (accept_3_3 8 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 121 (accept_3_3 5 55 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 121 (accept_3_3 2 55 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  121))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 121 (allA_succ_of_accept 53 54 121
  (accept_3_3 53 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 52 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 121 (accept_3_3 50 54 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 121 (Polychromatic418967fa.accept_14_7_12_9_1_2926 49 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 121
  (Polychromatic418967fa.accept_17_14_3_2_1_5848 48 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 121 (accept_3_3 47 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 121 (accept_3_3 44 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 121
  (Polychromatic418967fa.accept_19_4_16_7_1_5870 42 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 121 (accept_3_3 41 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 121 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 121 (accept_3_3 38 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 121 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 121
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 121 (accept_3_3 35 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 121 (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 121 (Polychromatic418967fa.accept_20_13_14_1_1_5869 33 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 121 (accept_3_3 32 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 121
  (Polychromatic418967fa.accept_20_10_14_1_1_5868 30 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 121 (accept_3_3 29 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 121 (Polychromatic418967fa.accept_17_11_3_2_1_5867 28 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 121 (accept_3_3 26 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 121 (accept_3_3 23 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 121 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 121 (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 121 (accept_3_3 20 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 121 (accept_3_3 17 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 121 (Polychromatic418967fa.accept_23_16_8_6_1_5866 16 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 121 (accept_3_3 14 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 121 (Polychromatic418967fa.accept_16_13_6_9_1_2561 13 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 121
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 121 (accept_3_3 11 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 121 (Polychromatic418967fa.accept_19_9_16_7_1_1056 9 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 121 (accept_3_3 8 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 121
  (Polychromatic418967fa.accept_13_6_2_4_1_923 6 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 121 (accept_3_3 5 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 54 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 121 (accept_3_3 2 54 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 121 (Polychromatic418967fa.accept_17_1_3_2_1_5846 1 54 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 121))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 121 (allA_of_3_1 53 53 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 121
  (allA_succ_of_accept 51 52 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 121 (accept_3_3 50 52 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 121 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 121 (accept_3_3 47 52
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 121 (Polychromatic418967fa.accept_9_1_7_4_1_52
  46 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 121 (accept_3_3 44 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 121 (accept_3_3 41 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 121 (accept_3_3 38 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 121 (accept_3_3 35 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 121 (accept_3_3 32 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 121 (Polychromatic418967fa.accept_19_12_14_7_1_5865 31 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 121 (accept_3_3 29 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 121 (accept_3_3 26 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 121 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 121 (accept_3_3 23 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 121 (accept_3_3 20 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 121 (Polychromatic418967fa.accept_19_18_14_7_1_5864 18 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 121 (accept_3_3 17 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 121 (accept_3_3 14 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 121 (accept_3_3 11 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 121 (accept_3_3 8 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  121 (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 52 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 121 (accept_3_3 5 52 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 121 (Polychromatic418967fa.accept_19_4_14_7_1_5863 4 52 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 121 (accept_3_3 2 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52
  121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 121)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 121 (allA_succ_of_accept 50 51 121
  (accept_3_3 50 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 121
  (Polychromatic418967fa.accept_19_11_13_7_1_5862 49 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 121 (accept_3_3 47 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 121 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 121 (accept_3_3 44
  51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 121
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 121 (accept_3_3 41 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 121 (accept_3_3 38 51
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 121 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 121
  (Polychromatic418967fa.accept_19_17_13_7_1_5861 36 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 121 (accept_3_3 35 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 121 (accept_3_3 32 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 121 (Polychromatic418967fa.accept_13_5_12_4_1_449 31 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 121 (accept_3_3 29 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 121 (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 121 (accept_3_3 26 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 121
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 121 (accept_3_3 23 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 121 (accept_3_3 20 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 121 (accept_3_3 17 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 121 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 121 (accept_3_3 14 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 121 (Polychromatic418967fa.accept_21_13_9_16_1_5860 13 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 121 (accept_3_3 11 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 121 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 121 (accept_3_3 8 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 121 (accept_3_3 5 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 121 (accept_3_3 2 51 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 121)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 121 (allA_of_3_1 50 50 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 121
  (allA_succ_of_accept 48 49 121 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 49 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 121 (accept_3_3 47 49 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 121 (Polychromatic418967fa.accept_13_7_10_4_1_919 46 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 121 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 121 (accept_3_3 44
  49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 121
  (Polychromatic418967fa.accept_21_1_7_16_1_5859 43 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 121 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 49 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 121 (accept_3_3 41 49 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 121 (Polychromatic418967fa.accept_13_1_10_4_1_954 40 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 121
  (Polychromatic418967fa.accept_22_17_5_11_1_2772 39 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 121 (accept_3_3 38 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 121 (Polychromatic418967fa.accept_13_11_10_4_1_1565 37 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 121 (Polychromatic418967fa.accept_25_11_24_21_1_4074 36 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 121 (accept_3_3 35 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 121 (Polychromatic418967fa.accept_13_8_10_4_1_2270 34 49
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 121
  (Polychromatic418967fa.accept_13_7_10_4_1_919 33 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 121 (accept_3_3 32 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 121 (Polychromatic418967fa.accept_13_5_10_4_1_1564 31 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 121 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 121 (accept_3_3 29 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 121 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 121
  (Polychromatic418967fa.accept_13_1_10_4_1_954 27 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 121 (accept_3_3 26 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 121 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 121 (Polychromatic418967fa.accept_13_11_10_4_1_1565 24 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 121 (accept_3_3 23 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 121 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 49 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 121
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 121 (accept_3_3 20 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 121 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 121 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 121 (accept_3_3 17 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 121 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 121
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 121 (accept_3_3 14 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 121 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 121 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 121 (accept_3_3 11 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 121 (Polychromatic418967fa.accept_16_10_1_9_1_4622 10 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 121
  (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 121 (accept_3_3 8 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  121 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 121 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 121 (accept_3_3 5 49 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 121 (Polychromatic418967fa.accept_17_4_15_2_1_4551 4 49 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 121
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 121 (accept_3_3 2 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  121 (Polychromatic418967fa.accept_13_1_10_4_1_954 1 49 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 121))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 121 (allA_succ_of_accept
  47 48 121 (accept_3_3 47 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 121 (accept_3_3 44 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 42
  48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 121 (accept_3_3 41 48
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 121
  (Polychromatic418967fa.accept_22_18_4_11_1_5858 40 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 121 (accept_3_3 38 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 121 (accept_3_3 35 48
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 121
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 121 (accept_3_3 32 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 121 (Polychromatic418967fa.accept_21_9_6_16_1_5857
  30 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 121 (accept_3_3 29
  48 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 121
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 121 (Polychromatic418967fa.accept_20_7_8_1_1_5856 27 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 121 (accept_3_3 26 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 121 (accept_3_3 23 48
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 121 (Polychromatic418967fa.accept_7_1_6_2_1_18
  22 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 121
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 121 (accept_3_3 20 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  48 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 121 (accept_3_3 17 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 121 (accept_3_3 14 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  48 121 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 121 (Polychromatic418967fa.accept_21_12_6_16_1_5855 12 48 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 121 (accept_3_3 11 48 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 48 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 121
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 48 121 (accept_3_3 8 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48
  121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 48 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 121 (accept_3_3 5 48 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 48 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 48 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 121 (accept_3_3 2 48 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  121)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 121 (allA_of_3_1 47 47 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 121 (allA_succ_of_accept 45 46 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 121 (accept_3_3 44 46 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 46 121 (accept_3_3 41 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  46 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 121 (accept_3_3 38 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 46 121 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 121
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 121 (accept_3_3 35 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  46 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 46 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 121 (accept_3_3 32 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 121 (accept_3_3 29 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  46 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 121 (accept_3_3 26 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 46 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 46 121 (accept_3_3 23 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  46 121 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 46 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 121 (accept_3_3 20 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 121
  (Polychromatic418967fa.accept_19_18_8_7_1_4446 18 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 46 121 (accept_3_3 17 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  46 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 121 (accept_3_3 14 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 121 (accept_3_3 11 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 121 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 121 (accept_3_3 8 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 121 (accept_3_3 5 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 46 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 46 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 121 (accept_3_3 2 46 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 121 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 46 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 121))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 45 121 (allA_succ_of_accept 44 45 121 (accept_3_3 44 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 45 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 121 (Polychromatic418967fa.accept_17_8_11_2_1_3415 42 45
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 121 (accept_3_3 41 45 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 121 (accept_3_3 38 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 121 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 121 (accept_3_3 35 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 121
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 121 (accept_3_3 32 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 121 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 121 (Polychromatic418967fa.accept_20_10_5_1_1_4406 30 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 121 (accept_3_3 29 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 121 (accept_3_3 26 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 121 (Polychromatic418967fa.accept_17_8_11_2_1_3415 25 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 121 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 121 (accept_3_3 23 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 121
  (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 121 (accept_3_3 20 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 121 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 121 (accept_3_3 17 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 121
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 121 (accept_3_3 14 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 121 (accept_3_3 11 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 121 (accept_3_3 8 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  121 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 121 (accept_3_3 5 45 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  45 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 121 (accept_3_3 2 45 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  121))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 121 (allA_of_3_1 44 44 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 121 (allA_succ_of_accept 42 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 121 (accept_3_3 41 43 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 121
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 121 (accept_3_3 38 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 121 (Polychromatic418967fa.accept_14_8_1_9_1_2085
  36 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 121 (accept_3_3 35
  43 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 43 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 121 (accept_3_3 32 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 43 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 121 (accept_3_3 29 43
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 121 (Polychromatic418967fa.accept_9_1_7_4_1_52
  28 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 121 (accept_3_3 26 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 121 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 121 (accept_3_3 23 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 121 (accept_3_3 20 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 121 (accept_3_3 17 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 121 (Polychromatic418967fa.accept_24_16_19_1_1_5854 16 43 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 121 (accept_3_3 14 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 121 (accept_3_3 11 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 121
  (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 121 (accept_3_3 8 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  121 (Polychromatic418967fa.accept_17_7_9_2_1_629 7 43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 121 (accept_3_3 5 43 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 121 (Polychromatic418967fa.accept_16_4_11_9_1_1631 4 43 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  43 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 121 (accept_3_3 2 43 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  121))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 121 (allA_succ_of_accept 41 42 121 (accept_3_3 41 42 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 121 (Polychromatic418967fa.accept_13_1_3_4_1_925
  40 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 121 (accept_3_3 38 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  42 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 42 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 121 (accept_3_3 35 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 121
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 42 121 (accept_3_3 32 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  42 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 42 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 121 (accept_3_3 29 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 42 121 (accept_3_3 26 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  42 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 42 121 (Polychromatic418967fa.accept_22_2_20_11_1_5852 24 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 121 (accept_3_3 23 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 121 (Polychromatic418967fa.accept_19_3_4_7_1_987 22 42 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 42 121 (accept_3_3 20 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  42 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 42 121 (Polychromatic418967fa.accept_26_18_16_17_1_5851 18 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 121 (accept_3_3 17 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 42 121 (accept_3_3 14 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  42 121 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 42 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 121 (accept_3_3 11 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 121
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 121 (accept_3_3 8 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42
  121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 42 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 121 (accept_3_3 5 42 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 42 121 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 42 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 121 (accept_3_3 2 42 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  121)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 121 (allA_of_3_1 41 41 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 121 (allA_succ_of_accept 39 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 121 (accept_3_3 38 40 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40 121 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  37 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 121
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 40 121 (accept_3_3 35 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  40 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 121 (accept_3_3 32 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 121
  (Polychromatic418967fa.accept_17_13_6_2_1_5850 30 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 121 (accept_3_3 29 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 121 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 121 (accept_3_3 26 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 121 (accept_3_3 23 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  40 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 121 (accept_3_3 20 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 40 121 (Polychromatic418967fa.accept_23_19_17_6_1_5849 19 40 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 121 (accept_3_3 17 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 121 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 121 (accept_3_3 14 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 121 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 40 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 121
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 121 (accept_3_3 11 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  40 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 121 (accept_3_3 8 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 121 (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 40 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 121
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 121 (accept_3_3 5 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40
  121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 40 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 40 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 121 (accept_3_3 2 40 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 40 121 (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 40 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 121)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 121
  (allA_succ_of_accept 38 39 121 (accept_3_3 38 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 121 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 121 (accept_3_3 35 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 121
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 121 (accept_3_3 32 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 121 (Polychromatic418967fa.accept_17_14_5_2_1_4559 31 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 121 (accept_3_3 29 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 121
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 121 (accept_3_3 26 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 121 (accept_3_3 23 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 121 (accept_3_3 20 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 121 (accept_3_3 17 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 121 (accept_3_3 14 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 121 (accept_3_3 11 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 121 (accept_3_3 8 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 121 (accept_3_3 5 39 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 121 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3
  39 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 121 (accept_3_3 2 39 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  121))))))))))))))))))))))))))))))))))))))) (allB_succ 38 121 (allA_of_3_1 38 38 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 121 (allA_succ_of_accept 36 37 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 121 (accept_3_3 35 37 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 34
  37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 121 (accept_3_3 32 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 121 (Polychromatic418967fa.accept_17_14_3_2_1_5848 31 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 121 (accept_3_3 29 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 121
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 121 (accept_3_3 26 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 121 (accept_3_3 23 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 121 (Polychromatic418967fa.accept_17_5_3_2_1_5847 22 37 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 121 (accept_3_3 20 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 121 (Polychromatic418967fa.accept_13_6_11_4_1_938 19 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 121 (Polychromatic418967fa.accept_17_1_3_2_1_5846 18 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 121 (accept_3_3 17 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 121
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 121 (accept_3_3 14 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 121 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 121 (accept_3_3 11 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 121 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 37 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 121
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 121 (accept_3_3 8 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 37 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 121 (accept_3_3 5 37 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 121 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 37 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 121 (accept_3_3 2 37 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 121 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1
  37 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  121))))))))))))))))))))))))))))))))))))) (allB_succ 36 121 (allA_succ_of_accept 35 36 121 (accept_3_3 35 36 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 34
  36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 121
  (Polychromatic418967fa.accept_13_7_10_4_1_919 33 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 121 (accept_3_3 32 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  36 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 121 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 121 (accept_3_3 29 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 121 (Polychromatic418967fa.accept_16_12_4_9_1_4633 28 36
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 121
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 121 (accept_3_3 26 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  36 121 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 36 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 121 (accept_3_3 23 36 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 121 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 121
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 36 121 (accept_3_3 20 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  36 121 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 36 121 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 121 (accept_3_3 17 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 121 (Polychromatic418967fa.accept_19_16_17_7_1_5845 16 36
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 121
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 36 121 (accept_3_3 14 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  36 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 36 121 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 121 (accept_3_3 11 36 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 36 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 121
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 121 (accept_3_3 8 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36
  121 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 36 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 121 (accept_3_3 5 36 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 36 121 (Polychromatic418967fa.accept_24_4_12_1_1_5844 4 36 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 121 (accept_3_3 2 36 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 121 (Polychromatic418967fa.accept_13_1_10_4_1_954 1
  36 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  121)))))))))))))))))))))))))))))))))))) (allB_succ 35 121 (allA_of_3_1 35 35 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 34 121 (allA_succ_of_accept 33 34 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 121 (accept_3_3 32 34 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 121 (accept_3_3 29 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  34 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 121 (accept_3_3 26 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 34 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 121 (accept_3_3 23 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  34 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 34 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 121 (accept_3_3 20 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 121 (accept_3_3 17 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  34 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 121 (accept_3_3 14 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 121 (Polychromatic418967fa.accept_19_13_15_7_1_5843 13 34 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 121 (accept_3_3 11 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  34 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 121 (accept_3_3 8 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 121 (accept_3_3 5 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34
  121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 34 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 121 (accept_3_3 2 34 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 121)))))))))))))))))))))))))))))))))) (allB_succ 33 121
  (allA_succ_of_accept 32 33 121 (accept_3_3 32 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  33 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 33 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 121 (accept_3_3 29 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 121
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 121 (accept_3_3 26 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 121 (accept_3_3 23 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 121 11 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 33 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 121 (accept_3_3 20 33 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 121
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 121 (accept_3_3 17 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 121 (accept_3_3 14 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 121 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 33 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 33 121 11 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 33 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 121 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 121 (accept_3_3 8 33 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7
  33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 121
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 121 (accept_3_3 5 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 121 (accept_3_3 2 33 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 121))))))))))))))))))))))))))))))))) (allB_succ 32 121
  (allA_of_3_1 32 32 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 121 (allA_succ_of_accept 30 31 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 121 (accept_3_3 29 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 121 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 121 (accept_3_3 26 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 121 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 121
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 121 (accept_3_3 23 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 121 (Polychromatic418967fa.accept_23_21_8_6_1_5842 21 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 121 (accept_3_3 20 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 121 (accept_3_3 17 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 121 (Polychromatic418967fa.accept_17_16_14_2_1_5841 16 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 121 (accept_3_3 14 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 121
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 121 (accept_3_3 11 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 121 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 121 (accept_3_3 8 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 121 (Polychromatic418967fa.accept_20_7_11_1_1_5840 7 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 121 (accept_3_3 5 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  121 (Polychromatic418967fa.accept_19_4_12_7_1_5839 4 31 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 121 (Polychromatic418967fa.accept_17_3_14_2_1_646 3 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 121 (accept_3_3 2 31 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 121))))))))))))))))))))))))))))))) (allB_succ 30 121
  (allA_succ_of_accept 29 30 121 (accept_3_3 29 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 121 (accept_3_3 26 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 30 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 121 (accept_3_3 23 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 121 (Polychromatic418967fa.accept_23_22_7_6_1_5838 22 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 121 (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 121 (accept_3_3 20 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 121
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 121 (accept_3_3 17 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 121 (accept_3_3 14 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 121 (Polychromatic418967fa.accept_19_13_11_7_1_4451 13 30 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 121
  (Polychromatic418967fa.accept_19_12_11_7_1_5837 12 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 121 (accept_3_3 11 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 121 (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 121 (accept_3_3 8 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 121 (accept_3_3 5 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  121 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 30 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 30 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 121 (accept_3_3 2 30 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 121)))))))))))))))))))))))))))))) (allB_succ 29 121
  (allA_of_3_1 29 29 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 121 (allA_succ_of_accept 27 28 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 121 (accept_3_3 26 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 121 (accept_3_3 23 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 121 (accept_3_3 20 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 121 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 121 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 121 (accept_3_3 17 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 121 (accept_3_3 14 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 121 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 121 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 121 (accept_3_3 11 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 121 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 121 (accept_3_3 8 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 121 (accept_3_3 5 28 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 121 (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 28 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 121 (accept_3_3 2 28 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 121 (Polychromatic418967fa.accept_18_1_10_13_1_500
  1 28 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 121))))))))))))))))))))))))))))
  (allB_succ 27 121 (allA_succ_of_accept 26 27 121 (accept_3_3 26 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 121 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 121 (accept_3_3 23 27 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 121 (accept_3_3 20 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 121 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 121 (accept_3_3 17 27 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 121
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 121 (accept_3_3 14 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 121 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 121 (Polychromatic418967fa.accept_17_12_10_2_1_5835 12 27 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 121 (accept_3_3 11 27 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 121
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 121 (accept_3_3 8 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  121 (Polychromatic418967fa.accept_21_7_6_16_1_5834 7 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 121 (accept_3_3 5 27 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 121
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 121 (accept_3_3 2 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 121))))))))))))))))))))))))))) (allB_succ 26 121 (allA_of_3_1 26 26 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 121 (allA_succ_of_accept 24 25 121 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 121 (accept_3_3 23 25 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 121 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  22 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 121 (accept_3_3 20 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 121 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 121 (accept_3_3 17 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 121 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 25 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 121 (accept_3_3 14 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 121 (accept_3_3 11 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 121 (accept_3_3 8 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  121 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 121 (accept_3_3 5 25 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 121 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 25 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 121 (accept_3_3 2 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 121))))))))))))))))))))))))) (allB_succ 24 121 (allA_succ_of_accept 23 24 121 (accept_3_3 23 24 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 22
  24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 121
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 121 (accept_3_3 20 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 121 (Polychromatic418967fa.accept_21_18_3_16_1_5833 18 24 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 121 (accept_3_3 17 24 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 121 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 24 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 121
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 121 (accept_3_3 14 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 121 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 121 (accept_3_3 11 24 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 121
  (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 121 (accept_3_3 8 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 121 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 121 (accept_3_3 5 24 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 121 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 24 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  24 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 121 (accept_3_3 2 24 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 121)))))))))))))))))))))))) (allB_succ
  23 121 (allA_of_3_1 23 23 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 121 (allA_succ_of_accept 21 22
  121 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 121 (accept_3_3 20 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 121 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 22 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 121 (accept_3_3 17 22 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 121 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 22 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 121 (accept_3_3 14 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 121 (Polychromatic418967fa.accept_19_12_3_7_1_5832 12 22 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 22 121 11 1 2 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 22 121
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 121 (accept_3_3 8 22 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 121 (accept_3_3 5 22 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4
  22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 121 (accept_3_3 2 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  121 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1 22 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 22 121)))))))))))))))))))))) (allB_succ 21 121 (allA_succ_of_accept 20 21 121 (accept_3_3 20 21
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 121 (Polychromatic418967fa.accept_9_1_3_4_1_47
  19 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 121
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 121 (accept_3_3 17 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 121 (accept_3_3 14 21 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 121 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 21 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 121
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 121 (accept_3_3 11 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 121 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 21 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 121 (accept_3_3 8 21 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 121
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 121 (accept_3_3 5 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 21 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 121 (accept_3_3 2 21 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 121))))))))))))))))))))) (allB_succ 20 121 (allA_of_3_1 20 20
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 121 (allA_succ_of_accept 18 19 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 121 (accept_3_3 17 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 121 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 121 (accept_3_3 14 19 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 121 (Polychromatic418967fa.accept_21_13_19_16_1_721 13 19 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 121
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 121 (accept_3_3 11 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 121 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 19 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 121 (accept_3_3 8 19 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 121 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 121 (accept_3_3 5 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 121 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 121 (accept_3_3 2 19 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 121 (Polychromatic418967fa.accept_21_1_19_16_1_2901 1 19 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 121))))))))))))))))))) (allB_succ 18 121 (allA_succ_of_accept 17
  18 121 (accept_3_3 17 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 121
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 121 (accept_3_3 14 18 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 121 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 121 (accept_3_3 11 18
  121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 121
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 121 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 121 (accept_3_3 8 18 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 121 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 121 (accept_3_3 5 18 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 121 (Polychromatic418967fa.accept_15_4_3_1_1_487 4
  18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 121
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 121 (accept_3_3 2 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  121 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 18 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 121)))))))))))))))))) (allB_succ 17 121 (allA_of_3_1 17 17 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 121 (allA_succ_of_accept 15 16 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 121 (accept_3_3 14 16 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 121 (Polychromatic418967fa.accept_22_13_16_11_1_5831 13 16
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 121
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 121 (accept_3_3 11 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 121 (accept_3_3 8 16 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 121 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 121
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 121 (accept_3_3 5 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  121 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 16 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 16 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 121 (accept_3_3 2 16 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 121)))))))))))))))) (allB_succ 15 121
  (allA_succ_of_accept 14 15 121 (accept_3_3 14 15 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 121 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 15 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 121 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 121 (accept_3_3 11 15 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 121
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 121 (accept_3_3 8 15 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  121 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 121 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 121 (accept_3_3 5 15 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 121 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  15 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 121 (accept_3_3 2 15 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 121 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 121))))))))))))))) (allB_succ 14 121
  (allA_of_3_1 14 14 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 121 (allA_succ_of_accept 12 13 121
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 121 (accept_3_3 11 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 121 (Polychromatic418967fa.accept_19_9_13_7_1_5830 9 13 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 121 (accept_3_3 8 13 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 121 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 13 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 121
  (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 121 (accept_3_3 5 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  121 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 121 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 121 (accept_3_3 2 13 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 121))))))))))))) (allB_succ 12 121 (allA_succ_of_accept 11 12
  121 (accept_3_3 11 12 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 12 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 121 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 121 (accept_3_3 8 12 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 121 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 121 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 121 (accept_3_3 5 12 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 121 (Polychromatic418967fa.accept_7_4_5_2_1_243 4
  12 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 121
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 121 (accept_3_3 2 12 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  121 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 121)))))))))))) (allB_succ 11 121 (allA_of_3_1 11 11 121 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 121 (allA_succ_of_accept 9 10 121 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 121 (accept_3_3 8 10 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 121
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 10 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 121 (accept_3_3 5 10 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  121 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 10 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 121 (accept_3_3 2 10 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 121)))))))))) (allB_succ 9 121 (allA_succ_of_accept 8
  9 121 (accept_3_3 8 9 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 121
  (Polychromatic418967fa.accept_13_7_9_4_1_918 7 9 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 121 (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 9 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 121 (accept_3_3 5 9 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 121 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 121 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 9
  121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 121 (accept_3_3 2 9 121
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 121 (Polychromatic418967fa.accept_27_1_9_13_1_5829 1
  9 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 121))))))))) (allB_succ 8 121
  (allA_of_3_1 8 8 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 121 (allA_succ_of_accept 6 7 121
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 121 (accept_3_3 5 7 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 121
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 7 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 121 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 121 (accept_3_3 2 7 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 121 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 121))))))) (allB_succ 6 121 (allA_succ_of_accept 5 6 121
  (accept_3_3 5 6 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 121
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 6 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 121 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 121 (accept_3_3 2 6 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 121 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 121)))))) (allB_succ 5 121 (allA_of_3_1 5 5 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 121 (allA_succ_of_accept 3 4 121
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 121 (accept_3_3 2 4 121 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 121
  (Polychromatic418967fa.accept_19_1_4_7_1_2018 1 4 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 121)))) (allB_succ 3 121 (allA_succ_of_accept 2 3 121 (accept_3_3 2 3 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 121 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 121))) (allB_succ 2 121 (allA_of_3_1 2 2 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


