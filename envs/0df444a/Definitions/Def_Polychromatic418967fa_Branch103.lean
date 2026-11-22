-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch103
-- name    : Polychromatic418967fa_Branch103
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:33.208525+00:00
-- url     : https://prove2.me/theorems/6bf27bdd-d345-4525-bebc-e19f19fd8f60
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

def Polychromatic418967fa.branch_103 : allB 103 103 :=
  allB_succ' 2 102 103 (Eq.refl Bool.true) (allA_succ_of_accept 1 102 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  102 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 103)) (allB_succ' 3 101 103
  (Eq.refl Bool.true) (allA_of_3_1 3 101 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 100 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 103 (accept_3_3 2 100 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 100 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 103)))) (allB_succ' 5 99 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 99 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 103 (accept_3_3 2 99 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 103 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  1 99 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 103))))) (allB_succ' 6 98 103
  (Eq.refl Bool.true) (allA_of_3_1 6 98 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 97 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 97 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 103 (accept_3_3 5 97 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 103 (accept_3_3 2 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 103))))))) (allB_succ' 8 96 103 (Eq.refl Bool.true) (allA_succ_of_accept 7 96 103
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 96 103 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 96 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 103 (accept_3_3 5 96 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 96 103 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 96 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  96 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 103 (accept_3_3 2 96 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 103)))))))) (allB_succ' 9 95 103
  (Eq.refl Bool.true) (allA_of_3_1 9 95 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 94 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 94 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 103 (accept_3_3 8 94 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 103 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 94 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 103
  (Polychromatic418967fa.accept_15_6_4_13_1_403 6 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 103 (accept_3_3 5 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  103 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 103 (accept_3_3 2 94 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 103)))))))))) (allB_succ' 11 93 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 93 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 103 (Polychromatic418967fa.accept_15_9_3_13_1_1686
  9 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 103 (accept_3_3 8 93
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 103 (Polychromatic418967fa.accept_9_7_3_4_1_218
  7 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 103 (accept_3_3 5 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 93 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 103 (accept_3_3 2 93 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 93 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 103))))))))))) (allB_succ' 12 92 103 (Eq.refl Bool.true)
  (allA_of_3_1 12 92 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 91 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 91 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 103 (accept_3_3 11 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 103 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 91 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 103
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 103 (accept_3_3 8 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 103 (accept_3_3 5 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 91 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 103 (accept_3_3 2 91 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 103 (Polychromatic418967fa.accept_19_1_15_8_1_4538
  1 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 103))))))))))))) (allB_succ' 14 90
  103 (Eq.refl Bool.true) (allA_succ_of_accept 13 90 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 103
  (Polychromatic418967fa.accept_20_12_10_3_1_4537 12 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 103 (accept_3_3 11 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 103 (Polychromatic418967fa.accept_23_10_21_11_1_4536 10 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 103 (accept_3_3 8 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 103 (Polychromatic418967fa.accept_19_7_14_8_1_4535 7 90 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 103
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 103 (accept_3_3 5 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 103 (Polychromatic418967fa.accept_16_3_10_7_1_4518 3 90 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 103 (accept_3_3 2 90 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 103)))))))))))))) (allB_succ' 15 89 103 (Eq.refl Bool.true)
  (allA_of_3_1 15 89 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 88 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 88 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 103 (accept_3_3 14 88 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 88 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 12
  88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 103 (accept_3_3 11 88
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 103 (Polychromatic418967fa.accept_9_1_7_4_1_52
  10 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 103 (accept_3_3 8 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  103 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 103 (accept_3_3 5 88 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 103 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 88 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 103 (accept_3_3 2 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  103 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 103)))))))))))))))) (allB_succ' 17 87 103 (Eq.refl Bool.true) (allA_succ_of_accept 16 87 103
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 87 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 103 (accept_3_3 14 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 103 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 87 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 103 (accept_3_3 11 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 103 (accept_3_3 8 87 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 103
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 103 (accept_3_3 5 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 103 (accept_3_3 2 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 103))))))))))))))))) (allB_succ' 18 86 103 (Eq.refl Bool.true)
  (allA_of_3_1 18 86 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 85 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 85 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 103 (accept_3_3 17 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 85 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 103
  (Polychromatic418967fa.accept_20_15_5_3_1_1953 15 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 103 (accept_3_3 14 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 103 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 103 (accept_3_3 11 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 103
  (Polychromatic418967fa.accept_25_9_10_3_1_1406 9 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 103 (accept_3_3 8 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  103 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 103 (accept_3_3 5 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 103 (accept_3_3 2 85 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 103 (Polychromatic418967fa.accept_11_1_8_4_1_717 1
  85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 103))))))))))))))))))) (allB_succ' 20
  84 103 (Eq.refl Bool.true) (allA_succ_of_accept 19 84 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 103
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 103 (accept_3_3 17 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 103 (accept_3_3 14 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 103 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 84 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 103
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 103 (accept_3_3 11 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 103 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 103 (accept_3_3 8 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 103 (accept_3_3 5 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  103 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 103 (accept_3_3 2 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 103)))))))))))))))))))) (allB_succ' 21 83 103
  (Eq.refl Bool.true) (allA_of_3_1 21 83 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 82 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 103 (accept_3_3 20 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 103 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 82 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 103
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 103 (accept_3_3 17 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 103 (accept_3_3 14 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 103 (accept_3_3 11 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 103 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 103 (accept_3_3 8 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 103 (accept_3_3 5 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  103 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 82 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 103 (accept_3_3 2 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 103)))))))))))))))))))))) (allB_succ' 23 81 103
  (Eq.refl Bool.true) (allA_succ_of_accept 22 81 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 103
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 103 (accept_3_3 20 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 103 (Polychromatic418967fa.accept_15_4_6_13_1_956 19 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 103 (accept_3_3 17 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 103
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 103 (accept_3_3 14 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 103 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 103 (accept_3_3 11 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 103
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 103 (accept_3_3 8 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  103 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 103 (accept_3_3 5 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 103
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 103 (accept_3_3 2 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  103 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 103))))))))))))))))))))))) (allB_succ' 24 80 103 (Eq.refl Bool.true) (allA_of_3_1 24 80 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 79 103 (Eq.refl Bool.true) (allA_succ_of_accept 24 79 103
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 103 (accept_3_3 23 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 103 (Polychromatic418967fa.accept_16_6_15_7_1_1510 22 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 103 (accept_3_3 20 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 103
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 103 (accept_3_3 17 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 103 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 103 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 103 (accept_3_3 14 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 103 (Polychromatic418967fa.accept_19_13_3_8_1_4534 13 79 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 103 (accept_3_3 11 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 103 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 103 (accept_3_3 8 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 103 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 79 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 103 (accept_3_3 5 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 103 (accept_3_3 2 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 103))))))))))))))))))))))))) (allB_succ' 26 78 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 103 (accept_3_3 23 78
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 103
  (Polychromatic418967fa.accept_20_2_18_3_1_4519 22 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 78 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 103 (accept_3_3 20 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 78 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 103 (accept_3_3 17 78
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 103
  (Polychromatic418967fa.accept_9_7_6_4_1_483 16 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 78 103 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 103 (accept_3_3 14 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 78 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 12
  78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 103 (accept_3_3 11 78
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 103 (Polychromatic418967fa.accept_7_3_1_5_1_44
  10 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 103 (accept_3_3 8 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78
  103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 103 (accept_3_3 5 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 103 (accept_3_3 2 78 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 103))))))))))))))))))))))))))
  (allB_succ' 27 77 103 (Eq.refl Bool.true) (allA_of_3_1 27 77 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  28 76 103 (Eq.refl Bool.true) (allA_succ_of_accept 27 76 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 103 (accept_3_3 26 76 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 103
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 103 (accept_3_3 23 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 103 (accept_3_3 20 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 76 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 103 (accept_3_3 17 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 103 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 103 (accept_3_3 14 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 103 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 76 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 103
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 12 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 103 (accept_3_3 11 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 103 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 103 (accept_3_3 8 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 103 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 76 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 103
  (Polychromatic418967fa.accept_21_6_13_19_1_4533 6 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 103 (accept_3_3 5 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 103 (accept_3_3 2 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 103)))))))))))))))))))))))))))) (allB_succ' 29 75 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 75 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 103 (Polychromatic418967fa.accept_10_7_5_3_1_542
  27 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 103 (accept_3_3 26
  75 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 103
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 75 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 103 (accept_3_3 23 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 75 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 103 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 103 (accept_3_3 20
  75 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 103
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 75 103 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 103 (accept_3_3 17 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 75 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 103 (accept_3_3 14 75
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 103
  (Polychromatic418967fa.accept_11_2_9_4_1_310 13 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 103 (accept_3_3 11 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 75 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 103 (accept_3_3 8 75 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 103 (accept_3_3 5 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 103 (Polychromatic418967fa.accept_16_3_11_7_1_770 3 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 103 (accept_3_3 2 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 103))))))))))))))))))))))))))))) (allB_succ' 30 74 103 (Eq.refl
  Bool.true) (allA_of_3_1 30 74 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 73 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 73 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 103 (accept_3_3 29 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 73 103 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 73 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 103
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 103 (accept_3_3 26 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 103 (accept_3_3 23 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 103 (accept_3_3 20 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 103 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 103 (accept_3_3 17 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 103
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 103 (accept_3_3 14 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 103 (Polychromatic418967fa.accept_16_13_9_7_1_4532 13 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 103 (accept_3_3 11 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 103
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 103 (accept_3_3 8 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 103 (accept_3_3 5 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 103 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 103 (accept_3_3 2 73 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 103)))))))))))))))))))))))))))))))
  (allB_succ' 32 72 103 (Eq.refl Bool.true) (allA_succ_of_accept 31 72 103 (Polychromatic418967fa.accept_7_3_2_5_1_147
  31 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 103
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 103 (accept_3_3 29 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 103 (Polychromatic418967fa.accept_16_12_8_7_1_4530 28 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 103 (Polychromatic418967fa.accept_25_2_22_3_1_4531 27 72 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 103 (accept_3_3 26 72 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 103
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 103 (accept_3_3 23 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 103 (Polychromatic418967fa.accept_17_5_4_1_1_3369 22 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 103 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 103 (accept_3_3 20 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 103 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 72 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 103
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 103 (accept_3_3 17 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 103 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 103 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 103 (accept_3_3 14 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 103 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 72 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 103
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 12 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 103 (accept_3_3 11 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 103 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 103 (accept_3_3 8 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 103 (Polychromatic418967fa.accept_14_7_2_5_1_4528 7 72 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 103
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 103 (accept_3_3 5 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 103 (accept_3_3 2 72 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 103 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 103)))))))))))))))))))))))))))))))) (allB_succ' 33 71 103
  (Eq.refl Bool.true) (allA_of_3_1 33 71 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 70 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 103 (accept_3_3 32 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 103 (accept_3_3 29 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 103 (accept_3_3 26 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 103 (accept_3_3 23 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 103 (Polychromatic418967fa.accept_19_3_13_8_1_4476 22 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 103 (accept_3_3 20 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 103
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 103 (accept_3_3 17 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 103 (accept_3_3 14 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 103 (accept_3_3 11 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 103 (accept_3_3 8 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 103 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 103 (accept_3_3 5 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  103 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 103 (accept_3_3 2 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 103)))))))))))))))))))))))))))))))))) (allB_succ' 35
  69 103 (Eq.refl Bool.true) (allA_succ_of_accept 34 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 103
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 103 (accept_3_3 32 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 103 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 103 (accept_3_3 29 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 103
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 103 (accept_3_3 26 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 103 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 103 (accept_3_3 23 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 103 (accept_3_3 20 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 103 (accept_3_3 17 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 103
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 103 (accept_3_3 14 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 103 (Polychromatic418967fa.accept_21_13_6_19_1_4489 13 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 103 (accept_3_3 11 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 103
  (Polychromatic418967fa.accept_22_9_3_15_1_4527 9 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 103 (accept_3_3 8 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 103 (accept_3_3 5 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 103 (accept_3_3 2 69 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 103)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 68 103 (Eq.refl Bool.true) (allA_of_3_1 36 68 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 67 103 (Eq.refl Bool.true) (allA_succ_of_accept 36 67 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 103 (accept_3_3 35 67 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 34
  67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 103
  (Polychromatic418967fa.accept_21_12_4_19_1_4526 33 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 103 (accept_3_3 32 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 103 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 103 (accept_3_3 29 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 103
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 103 (accept_3_3 26 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 103 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 103 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 103 (accept_3_3 23 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 103
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 103 (accept_3_3 20 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 103 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 103 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 103 (accept_3_3 17 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 103
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 103 (accept_3_3 14 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 103 (accept_3_3 11 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 103 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 103
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 103 (accept_3_3 8 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  103 (Polychromatic418967fa.accept_21_7_4_19_1_4525 7 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 103 (accept_3_3 5 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 67 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 103
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 103 (accept_3_3 2 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  103 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 103))))))))))))))))))))))))))))))))))))) (allB_succ' 38 66 103 (Eq.refl Bool.true) (allA_succ_of_accept
  37 66 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 103 (accept_3_3 35 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 103 (accept_3_3 32 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 103 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 103 (accept_3_3 29 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 103
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 103 (accept_3_3 26 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 103 (accept_3_3 23 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 103 (accept_3_3 20 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 103 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 103 (accept_3_3 17 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 103
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 103 (accept_3_3 14 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 103 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 103 (accept_3_3 11 66 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 103 (accept_3_3 8 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 103 (accept_3_3 5 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 103 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 103 (Polychromatic418967fa.accept_17_3_15_1_1_3348
  3 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 103 (accept_3_3 2 66
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  103)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 65 103 (Eq.refl Bool.true) (allA_of_3_1 39 65 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 64 103 (Eq.refl Bool.true) (allA_succ_of_accept 39 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 103 (accept_3_3 38 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 103 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 103 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 103 (accept_3_3 35 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 103 (accept_3_3 32 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 103 (accept_3_3 29 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 103 (Polychromatic418967fa.accept_19_9_7_8_1_3214 28 64 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 103 (accept_3_3 26 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 103 (accept_3_3 23 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 103 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 103 (accept_3_3 20 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 103 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 103 (accept_3_3 17 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 103 (accept_3_3 14 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 103 (accept_3_3 11 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 103 (accept_3_3 8 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 103 (accept_3_3 5 64 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 103 (accept_3_3 2 64 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 103 (Polychromatic418967fa.accept_18_1_10_13_1_500
  1 64 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  103)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 63 103 (Eq.refl Bool.true) (allA_succ_of_accept 40 63 103
  (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 103 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 103 (accept_3_3 38 63 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 103 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 103
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 103 (accept_3_3 35 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 103 (accept_3_3 32 63 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 103 (Polychromatic418967fa.accept_15_1_3_13_1_2548
  31 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 103
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 103 (accept_3_3 29 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 103 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 103 (accept_3_3 26 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 103 (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 63
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 103
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 103 (accept_3_3 23 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 103 (accept_3_3 20 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 103 (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 103
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 103 (accept_3_3 17 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 103 (Polychromatic418967fa.accept_17_15_12_1_1_3365 15 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 103 (accept_3_3 14 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 103 (Polychromatic418967fa.accept_17_13_12_1_1_4524 13 63
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 103
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 103 (accept_3_3 11 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 103 (accept_3_3 8 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 103 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 63 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 103
  (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 103 (accept_3_3 5 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 103 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 63 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 103 (accept_3_3 2 63 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 103 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 63 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 103))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 62
  103 (Eq.refl Bool.true) (allA_of_3_1 42 62 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 61 103 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 103 (accept_3_3 41 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 103 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 103 (accept_3_3 38 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 103 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 103 (accept_3_3 35 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 103 (accept_3_3 32 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 103 (Polychromatic418967fa.accept_17_14_10_1_1_4523 31 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 103 (accept_3_3 29 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 103
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 103 (accept_3_3 26 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 103 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 103 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 103 (accept_3_3 23 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 103 (accept_3_3 20 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 103 (accept_3_3 17 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 103 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 103 (accept_3_3 14 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 103 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 103 (accept_3_3 11 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 103
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 103 (accept_3_3 8 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  103 (Polychromatic418967fa.accept_17_7_10_1_1_4488 7 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 61 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 103 (accept_3_3 5 61 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 103 (Polychromatic418967fa.accept_16_4_13_7_1_4522 4 61 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 103 (accept_3_3 2 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61
  103 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 103))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 60 103 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 103 (Polychromatic418967fa.accept_17_8_9_1_1_3340 42 60 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 103 (accept_3_3 41 60 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 103 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  40 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 103 (accept_3_3 38 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  60 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 103 (accept_3_3 35 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 103
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 103 (accept_3_3 32 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  60 103 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 60 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 103 (accept_3_3 29 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 103
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 103 (accept_3_3 26 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  60 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 103 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 103 (accept_3_3 23 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 60 103 (accept_3_3 20 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  60 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 60 103 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 103 (accept_3_3 17 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 103
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 60 103 (accept_3_3 14 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  60 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 60 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 103 (accept_3_3 11 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 103
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 103 (accept_3_3 8 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60
  103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 103 (accept_3_3 5 60 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 103 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 60 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  60 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 103 (accept_3_3 2 60 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  103)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 59 103 (Eq.refl Bool.true) (allA_of_3_1 45 59 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 58 103 (Eq.refl Bool.true) (allA_succ_of_accept 45 58 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 103 (accept_3_3 44 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 103 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 103 (Polychromatic418967fa.accept_17_8_7_1_1_4521 42 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 103 (accept_3_3 41 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 103 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 103 (accept_3_3 38 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 103 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 103 (accept_3_3 35 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 103 (Polychromatic418967fa.accept_19_15_1_8_1_4520 34 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 103 (accept_3_3 32 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 103 (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 103 (accept_3_3 29 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 103 (accept_3_3 26 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 103 (accept_3_3 23 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 103 (Polychromatic418967fa.accept_20_2_18_3_1_4519 22 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 103 (accept_3_3 20 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 103 (Polychromatic418967fa.accept_16_3_10_7_1_4518 19 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 103 (accept_3_3 17 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 103 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 103 (accept_3_3 14 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 103 (Polychromatic418967fa.accept_19_12_1_8_1_4495 12 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 103 (accept_3_3 11 58 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 103 (accept_3_3 8 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  103 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 58 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 103 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 58 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 103 (accept_3_3 5 58 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 103 (accept_3_3 2 58 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  103)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 57 103 (Eq.refl Bool.true) (allA_succ_of_accept 46 57
  103 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 57 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 103 (accept_3_3 44 57 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 57 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 103 (accept_3_3 41 57
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 103 (Polychromatic418967fa.accept_6_4_3_1_1_57
  40 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 103
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 103 (accept_3_3 38 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 103 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 103 (accept_3_3 35 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 103 (accept_3_3 32 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 103 (accept_3_3 29 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 103
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 103 (accept_3_3 26 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 103 (accept_3_3 23 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 103
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 103 (accept_3_3 20 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 103 (accept_3_3 17 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 103 (accept_3_3 14 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 103 (Polychromatic418967fa.accept_17_12_6_1_1_4517 12 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 103 (accept_3_3 11 57 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 103
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 103 (accept_3_3 8 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 57 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 103 (accept_3_3 5 57 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 103 (accept_3_3 2 57 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  103))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 56 103 (Eq.refl Bool.true) (allA_of_3_1 48 56 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 55 103 (Eq.refl Bool.true) (allA_succ_of_accept 48 55 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 103 (accept_3_3 47 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 103 (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 103 (accept_3_3 44 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 103 (accept_3_3 41 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 103 (Polychromatic418967fa.accept_22_18_11_15_1_4515 40 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 103 (accept_3_3 38 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 103 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 103
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 103 (accept_3_3 35 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 103 (accept_3_3 32 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 103 (accept_3_3 29 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 103 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 103 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 103 (accept_3_3 26 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 103 (accept_3_3 23 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 103 (accept_3_3 20 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 103 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 103 (accept_3_3 17 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 103 (accept_3_3 14 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 103 (Polychromatic418967fa.accept_23_13_9_11_1_4514 13 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 103 (accept_3_3 11 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 103 (Polychromatic418967fa.accept_18_10_1_13_1_2192 10 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 103 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 103 (accept_3_3 8 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 103 (accept_3_3 5 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 55 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 103 (accept_3_3 2 55 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 103))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 54 103 (Eq.refl Bool.true) (allA_succ_of_accept 49 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 103
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 103 (accept_3_3 47 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 103 (Polychromatic418967fa.accept_21_4_12_19_1_4513 46 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 103 (accept_3_3 44 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 103 (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 103
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 103 (accept_3_3 41 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 103 (Polychromatic418967fa.accept_13_1_2_12_1_1299 40 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 103 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 103 (accept_3_3 38 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 103
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 103 (accept_3_3 35 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 103 (Polychromatic418967fa.accept_15_4_9_13_1_2582 34 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 103 (accept_3_3 32 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 103 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 103
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 103 (accept_3_3 29 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 103 (Polychromatic418967fa.accept_19_9_16_8_1_2097 28 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 103 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 103 (accept_3_3 26 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 103
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 103 (accept_3_3 23 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 103 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 103 (accept_3_3 20 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 103 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 103
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 103 (accept_3_3 17 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 103 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 103 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 103 (accept_3_3 14 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 103
  (Polychromatic418967fa.accept_22_12_10_15_1_4511 12 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 103 (accept_3_3 11 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 103 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 54 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 103 (accept_3_3 8 54 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 103 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 103
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 103 (accept_3_3 5 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  103 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 54 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 103 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 103 (accept_3_3 2 54 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 103))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 53 103 (Eq.refl Bool.true) (allA_of_3_1 51 53 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  52 103 (allA_succ_of_accept 51 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 103 (accept_3_3 50 52 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 103 (Polychromatic418967fa.accept_20_9_12_3_1_3191 49 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 103 (accept_3_3 47 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 103 (accept_3_3 44 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 103 (accept_3_3 41 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 103 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 103 (accept_3_3 38 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 103
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 103 (accept_3_3 35 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 103 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 103 (accept_3_3 32 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 103 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 103
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 103 (accept_3_3 29 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 103 (accept_3_3 26 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 103 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 103 (accept_3_3 23 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 103 (accept_3_3 20 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 103
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 103 (accept_3_3 17 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 103 (accept_3_3 14 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 103 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 103 (accept_3_3 11 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 103 (accept_3_3 8 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 103 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 103 (accept_3_3 5 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  103 (Polychromatic418967fa.accept_19_4_14_8_1_4510 4 52 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 103 (accept_3_3 2 52 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  103)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 103 (allA_succ_of_accept 50 51 103 (accept_3_3
  50 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 103
  (Polychromatic418967fa.accept_14_7_9_5_1_529 49 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 103 (accept_3_3 47 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 45
  51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 103 (accept_3_3 44 51
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 103
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 103 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 103 (accept_3_3 41 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 103 (accept_3_3 38 51
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 103 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 103 (accept_3_3 35 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 103 (accept_3_3 32 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 103 (accept_3_3 29 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 103 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 103 (accept_3_3 26 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 103
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 103 (accept_3_3 23 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 103 (accept_3_3 20 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 103
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 103 (accept_3_3 17 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 103 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 103 (accept_3_3 14 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 103 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 51
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 103 (accept_3_3 11 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 103 (accept_3_3 8 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 103
  (Polychromatic418967fa.accept_19_6_13_8_1_4508 6 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 103 (accept_3_3 5 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 103 (accept_3_3 2 51 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 103)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 103 (allA_of_3_1 50 50 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 103
  (allA_succ_of_accept 48 49 103 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 49 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 103 (accept_3_3 47 49 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 103
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 103 (accept_3_3 44 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 103 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 103 (accept_3_3 41 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 103 (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 103
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 103 (accept_3_3 38 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 103 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 103 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 103 (accept_3_3 35 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 103
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 103 (accept_3_3 32 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 103 (Polychromatic418967fa.accept_19_12_11_8_1_2091 31 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 103 (accept_3_3 29 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 103 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 103
  (Polychromatic418967fa.accept_25_2_24_3_1_4507 27 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 103 (accept_3_3 26 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 103 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 103 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 103 (accept_3_3 23 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 103
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 103 (accept_3_3 20 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 103 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 103 (accept_3_3 17 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 103 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 103
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 103 (accept_3_3 14 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 103 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 103 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 103 (accept_3_3 11 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 103
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 103 (accept_3_3 8 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  103 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 103 (accept_3_3 5 49 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 103 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 49 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 103
  (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 103 (accept_3_3 2 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  103 (Polychromatic418967fa.accept_19_1_11_8_1_4504 1 49 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 103))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 103 (allA_succ_of_accept
  47 48 103 (accept_3_3 47 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 103 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 103 (accept_3_3 44 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 42
  48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 103 (accept_3_3 41 48
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 103
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 103 (accept_3_3 38 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 103 (accept_3_3 35 48
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 103
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 103 (accept_3_3 32 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 103 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 103
  (Polychromatic418967fa.accept_17_13_14_1_1_2258 30 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 103 (accept_3_3 29 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 103 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 48 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 103 (accept_3_3 26 48 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 103 (accept_3_3 23 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 103 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 103 (accept_3_3 20 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 103 (accept_3_3 17 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 103 (accept_3_3 14 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 103 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 48 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 103
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 103 (accept_3_3 11 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 103 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 103 (accept_3_3 8 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 103 (accept_3_3 5 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 103 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 103 (accept_3_3 2 48 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 103)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 103 (allA_of_3_1 47 47 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 103 (allA_succ_of_accept 45 46
  103 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 103 (accept_3_3 44 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 103 (accept_3_3 41 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 103 (accept_3_3 38 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 103 (accept_3_3 35 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 103 (accept_3_3 32 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 103 (Polychromatic418967fa.accept_11_9_2_4_1_707 31 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 103 (accept_3_3 29 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 103 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 103 (accept_3_3 26 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 103 (accept_3_3 23 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 103 (accept_3_3 20 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 103 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 103 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 103 (accept_3_3 17 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 103 (accept_3_3 14 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 103 (accept_3_3 11 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 103 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 46 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 103 (accept_3_3 8 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 103 (accept_3_3 5 46 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 103 (accept_3_3 2 46 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  103)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 103 (allA_succ_of_accept 44 45 103 (accept_3_3 44 45
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 103 (Polychromatic418967fa.accept_7_1_3_5_1_33
  43 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 103 (accept_3_3 41 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 103 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 103 (accept_3_3 38 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 103
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 103 (accept_3_3 35 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 103 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 103 (accept_3_3 32 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 103 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 45
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 103 (accept_3_3 29 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 103 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 103 (accept_3_3 26 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 103 (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 103
  (Polychromatic418967fa.accept_17_7_11_1_1_4503 24 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 103 (accept_3_3 23 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 103 (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 103 (accept_3_3 20 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 103 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 45 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 103 (accept_3_3 17 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 103 (accept_3_3 14 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 103 (Polychromatic418967fa.accept_24_13_21_7_1_4502 13 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 103
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 103 (accept_3_3 11 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 103 (accept_3_3 8 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 103 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 103 (accept_3_3 5 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 103 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 103 (accept_3_3 2 45 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 103))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  103 (allA_of_3_1 44 44 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 103 (allA_succ_of_accept 42 43 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 103 (accept_3_3 41 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 103 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 103 (accept_3_3 38 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 103 (accept_3_3 35 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 103 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 103 (accept_3_3 32 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 103 (accept_3_3 29 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 103 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 103 (accept_3_3 26 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 103
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 103 (accept_3_3 23 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 103 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 103 (accept_3_3 20 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 103
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 103 (accept_3_3 17 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 103 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 103 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 103 (accept_3_3 14 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 103 (accept_3_3 11 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 103 (Polychromatic418967fa.accept_23_9_20_11_1_4501 9 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 103 (accept_3_3 8 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 103 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 103
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 103 (accept_3_3 5 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 103 (accept_3_3 2 43 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 103))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 103
  (allA_succ_of_accept 41 42 103 (accept_3_3 41 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 103 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 103 (accept_3_3 38 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 103
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 36 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 103 (accept_3_3 35 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 103 (accept_3_3 32 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 103 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 103 (accept_3_3 29 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 103 (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 103 (accept_3_3 26 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 103
  (Polychromatic418967fa.accept_11_2_9_4_1_310 24 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 103 (accept_3_3 23 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 103 (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 103 (accept_3_3 20 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 103
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 103 (accept_3_3 17 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 103 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 103 (accept_3_3 14 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 103 (accept_3_3 11 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 103 (accept_3_3 8 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 103
  (Polychromatic418967fa.accept_24_6_18_7_1_4498 6 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 103 (accept_3_3 5 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  103 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 42 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 103 (accept_3_3 2 42 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 103))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 41 103 (allA_of_3_1 41 41 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 103
  (allA_succ_of_accept 39 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 103 (accept_3_3 38 40 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 40 103 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 103
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 40 103 (accept_3_3 35 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  40 103 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 103 (accept_3_3 32 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 103 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 103
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 103 (accept_3_3 29 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 103 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 103 (accept_3_3 26 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 103 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 103
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 103 (accept_3_3 23 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  40 103 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 103 (accept_3_3 20 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 40 103 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 103
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 103 (accept_3_3 17 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 103 (accept_3_3 14 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 103 (Polychromatic418967fa.accept_19_13_2_8_1_4484 13 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 103
  (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 40 103 (accept_3_3 11 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 40 103 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 40 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 103 (accept_3_3 8 40 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 103 (Polychromatic418967fa.accept_14_7_12_5_1_1861
  7 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 103
  (Polychromatic418967fa.accept_19_6_2_8_1_4496 6 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 103 (accept_3_3 5 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40
  103 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 40 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 40 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 103 (accept_3_3 2 40 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 103 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 40 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 103))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 103 (allA_succ_of_accept 38 39 103 (accept_3_3 38 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 103 (accept_3_3 35 39 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 34
  39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 103 (accept_3_3 32 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 103 (Polychromatic418967fa.accept_19_12_1_8_1_4495 31 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 103 (accept_3_3 29 39 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 103
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 103 (accept_3_3 26 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 103 (accept_3_3 23 39 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 103
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 103 (accept_3_3 20 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 103 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 103 (accept_3_3 17 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 103
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 103 (accept_3_3 14 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 103 (Polychromatic418967fa.accept_18_12_3_13_1_4494 12 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 103 (accept_3_3 11 39 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 103
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 103 (accept_3_3 8 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 103 (accept_3_3 5 39 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 103 (Polychromatic418967fa.accept_15_3_9_13_1_1681
  3 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 103 (accept_3_3 2 39
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 103 (Polychromatic418967fa.accept_7_1_4_5_1_35
  1 39 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  103))))))))))))))))))))))))))))))))))))))) (allB_succ 38 103 (allA_of_3_1 38 38 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 103 (allA_succ_of_accept 36 37 103 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 103 (accept_3_3 35 37 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 103 (accept_3_3 32 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 103 (accept_3_3 29 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 103 (Polychromatic418967fa.accept_16_12_5_7_1_2360 28 37 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 103
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 103 (accept_3_3 26 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 103 (accept_3_3 23 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 103
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 103 (accept_3_3 20 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 103 (Polychromatic418967fa.accept_17_2_3_1_1_2244 19 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 103 (accept_3_3 17 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 103 (accept_3_3 14 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 103 (Polychromatic418967fa.accept_19_13_18_8_1_4493 13 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 103 (accept_3_3 11 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 103
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 103 (accept_3_3 8 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 103 (accept_3_3 5 37 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 103 (accept_3_3 2 37 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 103 (Polychromatic418967fa.accept_13_1_11_12_1_1322
  1 37 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  103))))))))))))))))))))))))))))))))))))) (allB_succ 36 103 (allA_succ_of_accept 35 36 103 (accept_3_3 35 36 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 34
  36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 103
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 103 (accept_3_3 32 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  36 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 103 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 103 (accept_3_3 29 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 103 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 103
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 103 (accept_3_3 26 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  36 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 36 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 103 (accept_3_3 23 36 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 103 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 103
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 36 103 (accept_3_3 20 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  36 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 36 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 103 (accept_3_3 17 36 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 103 (Polychromatic418967fa.accept_17_16_2_1_1_4492 16 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 103
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 36 103 (accept_3_3 14 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  36 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 36 103 (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 103 (accept_3_3 11 36 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 103
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 103 (accept_3_3 8 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36
  103 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 36 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 103 (accept_3_3 5 36 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 36 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 103 (accept_3_3 2 36 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 103 (Polychromatic418967fa.accept_21_1_15_19_1_4491
  1 36 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  103)))))))))))))))))))))))))))))))))))) (allB_succ 35 103 (allA_of_3_1 35 35 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 34 103 (allA_succ_of_accept 33 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 103 (accept_3_3 32 34 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 103 (Polychromatic418967fa.accept_13_5_8_12_1_2759
  31 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 103 (accept_3_3 29 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  34 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 34 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 103 (accept_3_3 26 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 103 (accept_3_3 23 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  34 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 103 (accept_3_3 20 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 103 (accept_3_3 17 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  34 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 34 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 103 (accept_3_3 14 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 103 (accept_3_3 11 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  34 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 103 (accept_3_3 8 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 103 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 34 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 103 (accept_3_3 5 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 103 (accept_3_3 2 34 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 103)))))))))))))))))))))))))))))))))) (allB_succ 33 103
  (allA_succ_of_accept 32 33 103 (accept_3_3 32 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  33 103 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 33 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 103 (accept_3_3 29 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 103
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 103 (accept_3_3 26 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 103 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 33 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 103 (accept_3_3 23 33 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 103 (accept_3_3 20 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 103 (accept_3_3 17 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 103
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 103 (accept_3_3 14 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 103 (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 103 (accept_3_3 11 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 103
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 103 (accept_3_3 8 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 103 (accept_3_3 5 33 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 103 (accept_3_3 2 33 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 103)))))))))))))))))))))))))))))))))
  (allB_succ 32 103 (allA_of_3_1 32 32 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 103
  (allA_succ_of_accept 30 31 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 103 (accept_3_3 29 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 103 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 31 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 103 (Polychromatic418967fa.accept_13_1_5_12_1_306
  27 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 103 (accept_3_3 26
  31 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 103
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 103 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 103 (accept_3_3 23 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 103 (Polychromatic418967fa.accept_13_8_5_12_1_2755
  21 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 103 (accept_3_3 20
  31 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 103
  (Polychromatic418967fa.accept_13_6_5_12_1_307 19 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 103 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 103 (accept_3_3 17 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 103 (accept_3_3 14 31
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 103
  (Polychromatic418967fa.accept_11_2_9_4_1_310 13 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 103 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 103 (accept_3_3 11 31 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 103 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 31 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 103
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 103 (accept_3_3 8 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  103 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 103 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 31 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 103 (accept_3_3 5 31 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 103 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 31 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 103
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 103 (accept_3_3 2 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 103))))))))))))))))))))))))))))))) (allB_succ 30 103 (allA_succ_of_accept 29 30 103 (accept_3_3 29 30 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 103
  (Polychromatic418967fa.accept_20_7_10_3_1_949 27 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 30 103 (accept_3_3 26 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  30 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 30 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 103 (accept_3_3 23 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 103 (Polychromatic418967fa.accept_19_3_11_8_1_3193 22 30 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 30 103 (accept_3_3 20 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  30 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 30 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 103 (accept_3_3 17 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 30 103
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 30 103 (accept_3_3 14 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  30 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 30 103 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 103 (accept_3_3 11 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 30 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 103 (accept_3_3 8 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 103 (accept_3_3 5 30 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  30 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 103 (accept_3_3 2 30 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 103))))))))))))))))))))))))))))))
  (allB_succ 29 103 (allA_of_3_1 29 29 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 103
  (allA_succ_of_accept 27 28 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 103 (accept_3_3 26 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 103 (accept_3_3 23 28
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 103
  (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 103 (accept_3_3 20 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 103 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 28 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 103 (Polychromatic418967fa.accept_13_5_2_12_1_1301
  18 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 103 (accept_3_3 17
  28 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 103
  (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 103 (accept_3_3 14 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 103 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 28 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 12
  28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 103 (accept_3_3 11 28
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 103
  (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 28 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 103 (accept_3_3 8 28 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 28 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 6
  28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 103 (accept_3_3 5 28 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 103 (Polychromatic418967fa.accept_13_4_2_12_1_2800
  4 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 103 (accept_3_3 2 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  103 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 28 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 103)))))))))))))))))))))))))))) (allB_succ 27 103 (allA_succ_of_accept 26 27 103 (accept_3_3 26 27 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 103 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 103
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 103 (accept_3_3 23 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 103 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 103 (accept_3_3 20 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 103 (Polychromatic418967fa.accept_16_3_11_7_1_770 19 27 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 103 (accept_3_3 17 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 103 (accept_3_3 14 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 103 (Polychromatic418967fa.accept_21_13_6_19_1_4489 13 27 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 103 (accept_3_3 11 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 103 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 103 (accept_3_3 8 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 103 (Polychromatic418967fa.accept_17_7_10_1_1_4488 7 27 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 103
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 103 (accept_3_3 5 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 103 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 27 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 103 (accept_3_3 2 27 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 103))))))))))))))))))))))))))) (allB_succ 26 103 (allA_of_3_1 26
  26 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 103 (allA_succ_of_accept 24 25 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 103 (accept_3_3 23 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 103 (accept_3_3 20 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 25 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 103 (accept_3_3 17 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 103 (accept_3_3 14 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 103 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 103
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 103 (accept_3_3 11 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 103 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 103 (accept_3_3 8 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 103 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 103 (accept_3_3 5 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  103 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 25 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 103 (accept_3_3 2 25 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 103))))))))))))))))))))))))) (allB_succ 24 103
  (allA_succ_of_accept 23 24 103 (accept_3_3 23 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 103 (accept_3_3 20 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 103
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 103 (accept_3_3 17 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 103 (accept_3_3 14 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 103 (Polychromatic418967fa.accept_19_13_5_8_1_4487 13 24 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 103
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 103 (accept_3_3 11 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 103 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 103 (accept_3_3 8 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 103
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 103 (accept_3_3 5 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  103 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 24 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 103 (accept_3_3 2 24 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 103)))))))))))))))))))))))) (allB_succ 23 103
  (allA_of_3_1 23 23 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 103 (allA_succ_of_accept 21 22 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 103 (accept_3_3 20 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 103 (Polychromatic418967fa.accept_20_19_2_3_1_4486 19 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 103 (accept_3_3 17 22 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 103 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 22 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 103 (accept_3_3 14 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 103 (Polychromatic418967fa.accept_21_12_1_19_1_4485 12 22 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 103 (accept_3_3 11 22 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 103
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 103 (accept_3_3 8 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  103 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 22 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 103 (accept_3_3 5 22 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 103 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 103 (accept_3_3 2 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 103)))))))))))))))))))))) (allB_succ 21 103 (allA_succ_of_accept 20 21 103 (accept_3_3 20 21 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 103 (accept_3_3 17 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 103 (accept_3_3 14 21 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 103 (Polychromatic418967fa.accept_19_13_2_8_1_4484 13 21 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 103
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 103 (accept_3_3 11 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 103 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 21 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 103 (accept_3_3 8 21 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 103 (accept_3_3 5 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 103 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 103 (accept_3_3 2 21 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 103))))))))))))))))))))) (allB_succ 20 103 (allA_of_3_1 20 20
  103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 103 (allA_succ_of_accept 18 19 103
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 103 (accept_3_3 17 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 103 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 103 (accept_3_3 14 19 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 103 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 19 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 103
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 103 (accept_3_3 11 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 103 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 103 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 19 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 103 (accept_3_3 8 19 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 103 (accept_3_3 5 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  103 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 19 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 103 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 103 (accept_3_3 2 19 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 103 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 19 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 103))))))))))))))))))) (allB_succ 18 103 (allA_succ_of_accept 17
  18 103 (accept_3_3 17 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 103
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 103 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 103 (accept_3_3 14 18 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 103
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 103 (accept_3_3 11 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 103 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 103 (accept_3_3 8 18 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 103 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 18 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 103
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 103 (accept_3_3 5 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  103 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 18 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 103 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 18 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 103 (accept_3_3 2 18 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 103)))))))))))))))))) (allB_succ 17 103 (allA_of_3_1
  17 17 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 103 (allA_succ_of_accept 15 16 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 103 (accept_3_3 14 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 103 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 103 (accept_3_3 11 16 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 103 (accept_3_3 8 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  103 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 16 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 103 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 103 (accept_3_3 5 16 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 103 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 103 (accept_3_3 2 16 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 103)))))))))))))))) (allB_succ 15 103
  (allA_succ_of_accept 14 15 103 (accept_3_3 14 15 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 103 (accept_3_3 11 15 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 103
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 15 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 103 (accept_3_3 8 15 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  103 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 103 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 103 (accept_3_3 5 15 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 103 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 103 (accept_3_3 2 15 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 103 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 103))))))))))))))) (allB_succ 14 103
  (allA_of_3_1 14 14 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 103 (allA_succ_of_accept 12 13 103
  (Polychromatic418967fa.accept_17_12_13_1_1_4478 12 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 103 (accept_3_3 11 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 103 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 13 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 103 (accept_3_3 8 13 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 103 (Polychromatic418967fa.accept_21_7_13_19_1_4477 7 13 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 103
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 103 (accept_3_3 5 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  103 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 103 (Polychromatic418967fa.accept_19_3_13_8_1_4476 3 13 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 103 (accept_3_3 2 13 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 103 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 103))))))))))))) (allB_succ 12 103 (allA_succ_of_accept 11 12
  103 (accept_3_3 11 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 103
  (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 103 (Polychromatic418967fa.accept_20_9_12_3_1_3191 9 12 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 103 (accept_3_3 8 12 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 103 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 103 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 103 (accept_3_3 5 12 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 103 (Polychromatic418967fa.accept_16_4_12_7_1_4475
  4 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 103
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 103 (accept_3_3 2 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  103 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 103)))))))))))) (allB_succ 11 103 (allA_of_3_1 11 11 103 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 103 (allA_succ_of_accept 9 10 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 103 (accept_3_3 8 10 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 103 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 103
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 103 (accept_3_3 5 10 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  103 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 10 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 103 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 103 (accept_3_3 2 10 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 103)))))))))) (allB_succ 9 103 (allA_succ_of_accept 8
  9 103 (accept_3_3 8 9 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 103
  (Polychromatic418967fa.accept_14_7_9_5_1_529 7 9 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 103 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 103 (accept_3_3 5 9 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 103 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 103 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 103 (accept_3_3 2 9 103
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 103 (Polychromatic418967fa.accept_19_1_9_8_1_4474 1
  9 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 103))))))))) (allB_succ 8 103
  (allA_of_3_1 8 8 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 103 (allA_succ_of_accept 6 7 103
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 103 (accept_3_3 5 7 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 103
  (Polychromatic418967fa.accept_10_4_7_3_1_54 4 7 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 103 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 103 (accept_3_3 2 7 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 103 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 103))))))) (allB_succ 6 103 (allA_succ_of_accept 5 6 103
  (accept_3_3 5 6 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 103
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 103 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 103 (accept_3_3 2 6 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 103 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 103)))))) (allB_succ 5 103 (allA_of_3_1 5 5 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 103 (allA_succ_of_accept 3 4 103
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 103 (accept_3_3 2 4 103 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 103
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 103)))) (allB_succ 3 103 (allA_succ_of_accept 2 3 103 (accept_3_3 2 3 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 103 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 103))) (allB_succ 2 103 (allA_of_3_1 2 2 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  103)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


