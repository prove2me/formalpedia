-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch155
-- name    : Polychromatic418967fa_Branch155
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:44.370098+00:00
-- url     : https://prove2.me/theorems/89b14fa2-2944-48c6-984e-ba9bc7bce91c
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

def Polychromatic418967fa.branch_155 : allB 155 155 :=
  allB_succ' 2 154 155 (Eq.refl Bool.true) (allA_of_3_0 2 154 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  153 155 (Eq.refl Bool.true) (allA_succ_of_accept 2 153 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 155 (accept_3_2 1 153 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 155))) (allB_succ' 4 152 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 152 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 152 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 155 (accept_3_2 1 152 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 155)))) (allB_succ' 5 151 155 (Eq.refl Bool.true) (allA_of_3_0
  5 151 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 150 155 (Eq.refl Bool.true) (allA_succ_of_gcd 5 150
  155 5 1 30 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  150 155 (accept_3_2 4 150 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 155
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 150 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 150 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 155 (accept_3_2 1 150 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 150 155)))))) (allB_succ' 7 149 155 (Eq.refl Bool.true) (allA_succ_of_accept 6 149 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 149 155 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 149 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 155 (accept_3_2 4 149 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 149 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 149 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2
  149 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 155 (accept_3_2 1 149
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149 155))))))) (allB_succ' 8 148 155 (Eq.refl Bool.true)
  (allA_of_3_0 8 148 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 147 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 155 (accept_3_2 7 147 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 5
  147 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 155 (accept_3_2 4 147
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 155
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 147 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 155 (accept_3_2 1 147 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 155))))))))) (allB_succ' 10 146 155 (Eq.refl Bool.true) (allA_succ_of_accept 9 146 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 146 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 146 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 155 (accept_3_2 7 146 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 146 155 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 146 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  146 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 155 (accept_3_2 4 146
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 155 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 146 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 146 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 155 (accept_3_2 1 146 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  155)))))))))) (allB_succ' 11 145 155 (Eq.refl Bool.true) (allA_of_3_0 11 145 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 144 155 (Eq.refl Bool.true) (allA_succ_of_accept 11 144 155
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 155 (accept_3_2 10 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 155 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 155 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 144 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 155 (accept_3_2 7 144 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 144 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 155 (accept_3_2 4 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 155 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 144 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 155 (accept_3_2 1 144 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 155)))))))))))) (allB_succ' 13 143 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 143 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 155 (accept_3_2 10 143 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  143 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 155
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 143 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 155 (accept_3_2 7 143 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 155 (accept_3_2 4 143 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 143 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 155 (accept_3_2 1 143 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  155))))))))))))) (allB_succ' 14 142 155 (Eq.refl Bool.true) (allA_of_3_0 14 142 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 141 155 (Eq.refl Bool.true) (allA_succ_of_accept 14 141 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 155 (accept_3_2 13 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 155 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 141 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 155 (accept_3_2 10 141 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 141 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 155 (accept_3_2 7 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 141 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 155 (accept_3_2 4 141 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 141 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 155 (accept_3_2 1 141 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  155))))))))))))))) (allB_succ' 16 140 155 (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 155 5 3 28 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 140 155
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 155 (accept_3_2 13 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 155 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 140 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 155 5 2 28 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 155
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 140 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 155 (accept_3_2 7 140 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 140 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 140 155 5 1 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 140 155 (accept_3_2 4 140 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 155
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 155 (accept_3_2 1 140 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  155)))))))))))))))) (allB_succ' 17 139 155 (Eq.refl Bool.true) (allA_of_3_0 17 139 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 138 155 (Eq.refl Bool.true) (allA_succ_of_accept 17 138 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 155 (accept_3_2 16 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 155 (accept_3_2 13 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 138 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 155 (accept_3_2 10 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 155 (accept_3_2 7 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 138 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 155 (accept_3_2 4 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 155 (accept_3_2 1 138 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138 155)))))))))))))))))) (allB_succ' 19 137 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 137 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 155 (accept_3_2 16 137 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 155
  (Polychromatic418967fa.accept_22_15_5_1_1_8441 15 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 137 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 155 (accept_3_2 13 137 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 137 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 155
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 155 (accept_3_2 10 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 155 (Polychromatic418967fa.accept_22_9_5_1_1_2204 9 137 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 137 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 155 (accept_3_2 7 137 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  137 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 155 (accept_3_2 4 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 155 (accept_3_2 1 137 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 155))))))))))))))))))) (allB_succ' 20 136 155 (Eq.refl Bool.true) (allA_of_3_0 20
  136 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 135 155 (Eq.refl Bool.true) (allA_succ_of_gcd 20 135
  155 5 4 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  135 155 (accept_3_2 19 135 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 155
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 18 135 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 135 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 155 (accept_3_2 16 135 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 135 155 5 3 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 135 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 155 (accept_3_2 13 135 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 135 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 155
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 11 135 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 135 155 5 2 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 135 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 155 (accept_3_2 7 135 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  135 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 155 5 1 27 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 155 (accept_3_2 4
  135 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 155 (accept_3_2 1 135 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 155))))))))))))))))))))) (allB_succ' 22 134 155 (Eq.refl Bool.true) (allA_succ_of_accept 21
  134 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 134 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 155 (accept_3_2 19 134 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 155 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 134
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 155 (accept_3_2 16 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 155 (accept_3_2 13 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 134 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 155
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 155 (accept_3_2 10 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 155 (accept_3_2 7 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 134 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 155 (accept_3_2 4 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 155 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 155 (accept_3_2 1 134 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 155)))))))))))))))))))))) (allB_succ' 23 133 155 (Eq.refl Bool.true) (allA_of_3_0
  23 133 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 132 155 (Eq.refl Bool.true) (allA_succ_of_accept 23
  132 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 132 155 (accept_3_2 22 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 132 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 155 (Polychromatic418967fa.accept_24_20_12_11_1_8440 20
  132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 155 (accept_3_2 19
  132 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 155
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 155 (accept_3_2 16 132 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 155 (Polychromatic418967fa.accept_9_5_6_2_1_161
  14 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 155 (accept_3_2 13
  132 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 155 (Polychromatic418967fa.accept_19_11_18_3_1_1755 11 132 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 155 (accept_3_2 10 132 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 155 (accept_3_2 7 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 155 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 155 (accept_3_2 4 132 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 155 (accept_3_2 1 132 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  155)))))))))))))))))))))))) (allB_succ' 25 131 155 (Eq.refl Bool.true) (allA_succ_of_accept 24 131 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 131 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 155 (accept_3_2 22 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 131 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 131 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 155 (Polychromatic418967fa.accept_7_6_5_1_1_416
  20 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 155 (accept_3_2 19
  131 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 131 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 155 (accept_3_2 16 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 131 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 131 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 155 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  14 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 155 (accept_3_2 13
  131 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 155
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 131 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 155 (accept_3_2 10 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 131 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 131 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 155 (accept_3_2 7 131
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 131 155 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 155 (accept_3_2 4 131 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 131 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 131 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 155 (accept_3_2 1
  131 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131 155))))))))))))))))))))))))) (allB_succ' 26 130 155
  (Eq.refl Bool.true) (allA_of_3_0 26 130 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 129 155 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 129 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 155 (accept_3_2 25 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 155 (accept_3_2 22 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 155 (accept_3_2 19 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 155 (accept_3_2 16 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 155 (accept_3_2 13 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 155 (accept_3_2 10 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 155 (accept_3_2 7 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 155 (accept_3_2 4 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 155 (accept_3_2 1 129 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 155))))))))))))))))))))))))))) (allB_succ' 28 128 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 128
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 155 (accept_3_2 25 128
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 128 155 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 155 (accept_3_2 22 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 128 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 155 (Polychromatic418967fa.accept_7_6_2_1_1_214
  20 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 155 (accept_3_2 19
  128 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 155
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 128 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 155 (accept_3_2 16 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 128 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 155 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 155 (accept_3_2 13
  128 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 155
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 128 155 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 155 (accept_3_2 10 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 128 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 155 (Polychromatic418967fa.accept_14_8_2_1_1_1652
  8 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 155 (accept_3_2 7
  128 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 155
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 128 155 (Polychromatic418967fa.accept_19_5_14_3_1_4187 5 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 155 (accept_3_2 4 128 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 128 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  128 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 155 (accept_3_2 1 128
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 155)))))))))))))))))))))))))))) (allB_succ' 29 127 155
  (Eq.refl Bool.true) (allA_of_3_0 29 127 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 126 155 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 155 (accept_3_2 28 126 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 126 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 155
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 155 (accept_3_2 25 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 155 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 155 (accept_3_2 22 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 155
  (Polychromatic418967fa.accept_28_20_14_15_1_8439 20 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 126 155 (accept_3_2 19 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 126 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 126 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 155 (accept_3_2 16 126 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 155
  (Polychromatic418967fa.accept_17_15_7_2_1_2303 15 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 126 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 155 (accept_3_2 13 126 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 155
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 155 (accept_3_2 10 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  126 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 126 155 (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 155 (accept_3_2 7 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 155 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 126 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 155 (accept_3_2 4 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  126 155 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 126 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 126 155 (Polychromatic418967fa.accept_19_2_12_3_1_5446 2 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 155 (accept_3_2 1 126 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126 155)))))))))))))))))))))))))))))) (allB_succ' 31 125 155 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 125 155 5 6 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 125 155 (Polychromatic418967fa.accept_17_12_6_2_1_2346 29 125 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 155 (accept_3_2 28 125 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 155 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 125
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 125 155 5 5 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 125 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 155 (accept_3_2 22 125 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 155 (Polychromatic418967fa.accept_9_3_8_2_1_162
  21 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 155 5 4 25 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 155
  (accept_3_2 19 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 155 (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 125 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 155 (accept_3_2 16 125 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 125 155 5 3 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 125 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 155 (accept_3_2 13 125 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 155
  (Polychromatic418967fa.accept_20_11_5_15_1_8438 11 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 125 155 5 2 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 125 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 155
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 155 (accept_3_2 7 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 125 155 5 1 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 125 155 (accept_3_2 4 125 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 125 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 125 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 155 (accept_3_2 1 125 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125 155))))))))))))))))))))))))))))))) (allB_succ' 32 124 155
  (Eq.refl Bool.true) (allA_of_3_0 32 124 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 123 155 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 155 (accept_3_2 31 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 155
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 29 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 155 (accept_3_2 28 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 155 (accept_3_2 25 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 155 (accept_3_2 22 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 155 (accept_3_2 19 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 123 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 155 (accept_3_2 16 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 155 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 155 (accept_3_2 13 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 155
  (Polychromatic418967fa.accept_19_11_9_3_1_4167 11 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 155 (accept_3_2 10 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 155 (accept_3_2 7 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 123 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 155 (accept_3_2 4 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 155 (accept_3_2 1 123 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 155))))))))))))))))))))))))))))))))) (allB_succ' 34 122 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 122 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 122 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 155 (accept_3_2 31 122 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 155 (accept_3_2 28 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 155 (accept_3_2 25 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 155 (accept_3_2 22 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 155 (accept_3_2 19 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 122 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 155 (accept_3_2 16 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 155 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 155 (accept_3_2 13 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 122 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 155 (accept_3_2 10 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 155 (accept_3_2 7 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 122 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 155 (accept_3_2 4 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 155 (accept_3_2 1 122 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 155)))))))))))))))))))))))))))))))))) (allB_succ' 35 121 155 (Eq.refl Bool.true)
  (allA_of_3_0 35 121 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 120 155 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 120 155 5 7 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 120 155 (accept_3_2 34 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 120 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 120 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 120 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 155 (accept_3_2 31 120 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 155 5 6 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 155 (Polychromatic418967fa.accept_16_13_8_11_1_4785 29 120
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 155 (accept_3_2 28 120
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 155
  (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 120 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 120 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 120 155 5 5 24 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 120 155
  (Polychromatic418967fa.accept_9_6_3_2_1_431 24 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 155 (accept_3_2 22 120 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 155 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 120 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 155 5 4 24 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 155 (accept_3_2 19 120 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 155
  (Polychromatic418967fa.accept_19_18_6_3_1_8405 18 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 120 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 155 (accept_3_2 16 120 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 120 155 5 3 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 120 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 155 (accept_3_2 13 120 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 155 (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 120
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 155
  (Polychromatic418967fa.accept_22_11_10_1_1_8437 11 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 155 5 2 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 120 155 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 120 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 155 (accept_3_2 7 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 120 155 5 1 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 120 155 (accept_3_2 4 120 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 120 155 (Polychromatic418967fa.accept_16_3_8_11_1_2714 3 120 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 120
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 155 (accept_3_2 1 120 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 155)))))))))))))))))))))))))))))))))))) (allB_succ' 37 119 155
  (Eq.refl Bool.true) (allA_succ_of_accept 36 119 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 155
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 155 (accept_3_2 34 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 155 (Polychromatic418967fa.accept_19_14_5_3_1_859 33 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 155 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 155 (accept_3_2 31 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 155 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 119
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 155
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 155 (accept_3_2 28 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 155 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 155 (accept_3_2 25 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 155 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 119 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 155
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 119 155 (accept_3_2 22 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 119 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 119 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 119 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 155 (accept_3_2 19 119 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 155
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 119 155 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 119 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 155 (accept_3_2 16 119 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 119 155 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 155
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 155 (accept_3_2 13 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 155 (accept_3_2 10 119 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 155 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 155
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 155 (accept_3_2 7 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 155 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 155 (accept_3_2 4 119 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 155 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 119
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 155
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 155 (accept_3_2 1 119 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  155))))))))))))))))))))))))))))))))))))) (allB_succ' 38 118 155 (Eq.refl Bool.true) (allA_of_3_0 38 118 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 117 155 (Eq.refl Bool.true) (allA_succ_of_accept 38 117 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 155 (accept_3_2 37 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 155 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 155 (Polychromatic418967fa.accept_21_14_12_8_1_6833 35 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 155 (accept_3_2 34 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 155 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 155 (accept_3_2 31 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 155 (Polychromatic418967fa.accept_23_6_2_17_1_8436 29 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 155 (accept_3_2 28 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 155 (accept_3_2 25 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 155 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 155 (accept_3_2 22 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 155 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 117
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 155 (accept_3_2 19 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 155 (accept_3_2 16 117 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 155 (accept_3_2 13 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 117 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 155 (accept_3_2 10 117 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 155 (accept_3_2 7 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 155 (Polychromatic418967fa.accept_20_5_17_15_1_6858 5 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 155 (accept_3_2 4 117 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 155 (accept_3_2 1 117 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  155))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 116 155 (Eq.refl Bool.true) (allA_succ_of_accept 39 116 155
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 116 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 116 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 155 (accept_3_2 37 116 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 116 155 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 155
  (Polychromatic418967fa.accept_19_16_2_3_1_5479 35 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 155 (accept_3_2 34 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 155 (accept_3_2 31 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 155
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 155 (accept_3_2 28 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 155 (accept_3_2 25 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 155 (accept_3_2 22 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 155 (Polychromatic418967fa.accept_17_3_14_2_1_646 20 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 155 (accept_3_2 19 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 116
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 155 (accept_3_2 16 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 155 (accept_3_2 13 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 155
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 155 (accept_3_2 10 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 155 (accept_3_2 7 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 116 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 155 (accept_3_2 4 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 155 (accept_3_2 1 116 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 155)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 115 155 (Eq.refl
  Bool.true) (allA_of_3_0 41 115 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 114 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 155 (accept_3_2 40 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 155 (Polychromatic418967fa.accept_7_3_2_1_1_225
  38 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 155 (accept_3_2 37
  114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 155
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 155 (accept_3_2 34 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 155 (Polychromatic418967fa.accept_9_5_6_2_1_161
  32 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 155 (accept_3_2 31
  114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 155
  (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 155 (accept_3_2 28 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 155 (Polychromatic418967fa.accept_9_8_6_2_1_744
  26 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 155 (accept_3_2 25
  114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 155 (accept_3_2 22 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 155 (Polychromatic418967fa.accept_7_6_2_1_1_214
  20 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 155 (accept_3_2 19
  114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 155
  (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 155 (accept_3_2 16 114 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 155 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 114 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 155 (accept_3_2 13 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 114 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 155 (accept_3_2 10 114 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 155 (accept_3_2 7 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 155 (accept_3_2 4 114 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 114 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 155
  (Polychromatic418967fa.accept_13_2_10_12_1_757 2 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 155 (accept_3_2 1 114 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  155)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 113 155 (Eq.refl Bool.true) (allA_succ_of_accept 42 113
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 155 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 113 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 155 (accept_3_2 40 113 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 113 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 155 (accept_3_2 37
  113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 155
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 155 (accept_3_2 34 113 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 155
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 155 (accept_3_2 31 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 155 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 155 (accept_3_2 28 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 113
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 155 (accept_3_2 25 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 155 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 155 (accept_3_2 22 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 155
  (Polychromatic418967fa.accept_17_3_11_2_1_8435 20 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 155 (accept_3_2 19 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 155 (accept_3_2 16 113 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 155 (accept_3_2 13 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 155 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 155 (accept_3_2 10 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 155 (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 113
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 155 (accept_3_2 7 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 155 (Polychromatic418967fa.accept_20_5_13_15_1_8434 5 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 155 (accept_3_2 4 113 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 113 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 155 (accept_3_2 1 113 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  155))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 112 155 (Eq.refl Bool.true) (allA_of_3_0 44 112 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 111 155 (Eq.refl Bool.true) (allA_succ_of_accept 44 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 155 (accept_3_2 43 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 155 (accept_3_2 40 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 155 (accept_3_2 37 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 155 (accept_3_2 34 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 155 (accept_3_2 31 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 155 (accept_3_2 28 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 111
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 155 (accept_3_2 25 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 155 (accept_3_2 22 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 155 (accept_3_2 19 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 155 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 155 (accept_3_2 16 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 155 (accept_3_2 13 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 155 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 155 (accept_3_2 10 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 155 (accept_3_2 7 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 155 (accept_3_2 4 111 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 111 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 155 (accept_3_2 1 111 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  155))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 110 155 (Eq.refl Bool.true) (allA_succ_of_gcd 45 110
  155 5 9 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  110 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 110 155 (accept_3_2 43 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 110 155 (Polychromatic418967fa.accept_20_2_10_15_1_3953 42 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 155 5 8 22 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 155
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 110 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 110 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 155 (accept_3_2 37 110 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 110 155 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 110 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 110 155 5 7 22 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 110 155 (accept_3_2 34 110 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 155 (accept_3_2 31 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  110 155 5 6 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 110 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 110 155 (accept_3_2 28 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 110 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 155 (Polychromatic418967fa.accept_19_7_15_3_1_2896 26 110
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 110 155 5 5 22 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 110 155 (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 155 (accept_3_2 22 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 155 5 4 22 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 155 (accept_3_2 19 110 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 155 (Polychromatic418967fa.accept_7_4_5_1_1_418
  18 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 155 (accept_3_2 16 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  110 155 5 3 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 110 155 (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 110 155 (accept_3_2 13 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 155 (Polychromatic418967fa.accept_19_12_15_3_1_8433 12 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 155 (Polychromatic418967fa.accept_7_4_5_1_1_418
  11 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 155 5 2 22 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 110 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 155 (accept_3_2 7 110 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 155 5 1 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 155 (accept_3_2 4 110 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 155
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 155 (accept_3_2 1 110 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  155)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 109 155 (Eq.refl Bool.true) (allA_of_3_0 47 109 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 108 155 (Eq.refl Bool.true) (allA_succ_of_accept 47 108 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 155 (accept_3_2 46 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 108 155 (Polychromatic418967fa.accept_19_7_13_3_1_4171 45 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 108 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 155 (accept_3_2 43 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 155
  (Polychromatic418967fa.accept_13_2_4_12_1_745 41 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 155 (accept_3_2 40 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 108 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 108 155 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 155 (accept_3_2 37 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 108
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 155
  (Polychromatic418967fa.accept_17_1_6_2_1_623 35 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 155 (accept_3_2 34 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 108 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 108 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 155 (accept_3_2 31 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 155
  (Polychromatic418967fa.accept_13_3_4_12_1_36 29 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 155 (accept_3_2 28 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 155 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 155 (accept_3_2 25 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 155 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 108 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 155 (accept_3_2 22 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 155 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 155 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 155 (accept_3_2 19 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 108 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 155
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 155 (accept_3_2 16 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 155 (Polychromatic418967fa.accept_20_14_8_15_1_8432 14 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 155 (accept_3_2 13 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 155 (accept_3_2 10 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 155 (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 155 (accept_3_2 7 108 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 108 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 155 (accept_3_2 4 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 155 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 155 (accept_3_2 1 108 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 155)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 107 155 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 107 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 155
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 155 (accept_3_2 46 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 155 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 155 (accept_3_2 43 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 155
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 155 (accept_3_2 40 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 155 (accept_3_2 37 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 155 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 155
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 155 (accept_3_2 34 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 155 (accept_3_2 31 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 155 (accept_3_2 28 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 155 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 155 (accept_3_2 25 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 155 (accept_3_2 22 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 155 (accept_3_2 19 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 155 (accept_3_2 16 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 155 (accept_3_2 13 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 155
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 155 (accept_3_2 10 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 155 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 155 (accept_3_2 7 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 155 (accept_3_2 4 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 155 (accept_3_2 1 107 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 155))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 106 155
  (Eq.refl Bool.true) (allA_of_3_0 50 106 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 105 155 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 105 155 5 10 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 105 155 (accept_3_2 49 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 105 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 155 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 105
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 155 (accept_3_2 46 105
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 155 5 9 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 155 (accept_3_2 43 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 105 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 155 5 8 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 155
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 155 (accept_3_2 37 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 155 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 105 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 155 5 7 21 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 155 (accept_3_2 34 105 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 155
  (Polychromatic418967fa.accept_20_13_5_15_1_8431 33 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 155 (accept_3_2 31 105 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 155 5 6 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 105
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 155 (accept_3_2 28 105
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 155
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 155 5 5 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 155 (Polychromatic418967fa.accept_13_11_1_12_1_742
  24 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 155 (accept_3_2 22 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 105 155 5 4 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 105 155 (accept_3_2 19 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 155 (accept_3_2 16 105 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 155 5 3 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 155 (accept_3_2 13 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 155 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 105 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 155 5 2 21 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 155
  (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 155 (accept_3_2 7 105 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 155 5 1 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 155 (accept_3_2 4 105 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 155 (accept_3_2 1 105 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  155))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 104 155 (Eq.refl Bool.true) (allA_succ_of_accept
  51 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 155 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 155 (accept_3_2 49 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 155 (accept_3_2 46 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 155 (accept_3_2 43 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 155
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 155 (accept_3_2 40 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 155 (accept_3_2 37 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 104
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 155 (accept_3_2 34 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 155 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 155 (accept_3_2 31 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 104 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 155
  (Polychromatic418967fa.accept_10_9_4_5_1_616 29 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 155 (accept_3_2 28 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 155 (accept_3_2 25 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 155 (accept_3_2 22 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 155 (Polychromatic418967fa.accept_16_4_8_11_1_5961 20 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 155 (accept_3_2 19 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 155 (Polychromatic418967fa.accept_19_18_9_3_1_8430 18 104
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 155 (accept_3_2 16 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 155 (accept_3_2 13 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 104 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 155
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 155 (accept_3_2 10 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 155 (accept_3_2 7 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 155 (accept_3_2 4 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 155 (accept_3_2 1 104 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 155)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 103 155
  (Eq.refl Bool.true) (allA_of_3_0 53 103 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 102 155 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 155 (accept_3_2 52 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 155 (accept_3_2 49 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 155 (accept_3_2 46 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 155 (accept_3_2 43 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 155 (accept_3_2 40 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 155 (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 102 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 155 (accept_3_2 37 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 155 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 155 (accept_3_2 34 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 155 (accept_3_2 31 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 155 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 155 (accept_3_2 28 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 155 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 155 (accept_3_2 25 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 155 (accept_3_2 22 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 155
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 102 155 (accept_3_2 19 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 102 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 155 (accept_3_2 16 102 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 155 (Polychromatic418967fa.accept_9_6_3_2_1_431
  15 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 155 (accept_3_2 13 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 155 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 155 (accept_3_2 10 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 155 (accept_3_2 7 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 155 (accept_3_2 4 102 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 155
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 155 (accept_3_2 1 102 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 101 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 155 (accept_3_2 52 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 51
  101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 155 (accept_3_2 49 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 155 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 155 (accept_3_2 46 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 155 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 155 (accept_3_2 43 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 155 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 155 (accept_3_2 40 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 155 (accept_3_2 37 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 155 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 155 (accept_3_2 34 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 155 (accept_3_2 31 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 155 (accept_3_2 28 101 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 155 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 101
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 155 (accept_3_2 25 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 155 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 155 (accept_3_2 22 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 155 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 101 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 155
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 101 155 (accept_3_2 19 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 155 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 101
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 155 (accept_3_2 16 101
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 155
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 155 (accept_3_2 13 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 155 (accept_3_2 10
  101 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 101 155 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 155 (accept_3_2 7 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 155 (accept_3_2 4 101
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 155
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 101 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 101 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 155 (accept_3_2 1 101 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 101 155))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 100 155 (Eq.refl
  Bool.true) (allA_of_3_0 56 100 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 99 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 155 (accept_3_2 55 99 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 155 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 155 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  53 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 155 (accept_3_2 52
  99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 155
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 155 (accept_3_2 49 99 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 155 (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 155
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 47 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 155 (accept_3_2 46 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 155 (accept_3_2 43 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 155 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 155
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 155 (accept_3_2 40 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 155 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 155 (accept_3_2 37 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 155
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 155 (accept_3_2 34 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 155 (accept_3_2 31 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 155 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 155
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 155 (accept_3_2 28 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 155 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 155 (accept_3_2 25 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 155 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 155
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 155 (accept_3_2 22 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 155 (accept_3_2 19 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 155 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 155
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 155 (accept_3_2 16 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 155 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 155 (accept_3_2 13 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 155 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 155
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 155 (accept_3_2 10 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 155 (accept_3_2 7 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 99 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 155
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 155 (accept_3_2 4 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  155 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 99 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 99 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 155 (accept_3_2 1 99 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 99 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 98 155
  (Eq.refl Bool.true) (allA_succ_of_accept 57 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 155
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 155 (accept_3_2 55 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 155 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 155 (accept_3_2 52 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 155 (accept_3_2 49 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 155 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 155 (accept_3_2 46 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 155
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 155 (accept_3_2 43 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 155 (accept_3_2 40 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 155
  (Polychromatic418967fa.accept_16_6_2_11_1_7132 38 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 155 (accept_3_2 37 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 155 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 155 (accept_3_2 34 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 155 (accept_3_2 31 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 155 (accept_3_2 28 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 155
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 155 (accept_3_2 25 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 155 (accept_3_2 22 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 155
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 155 (accept_3_2 19 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 155 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 155 (accept_3_2 16 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 155 (accept_3_2 13 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 155 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 155 (accept_3_2 10 98 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 155
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 155 (accept_3_2 7 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 155 (accept_3_2 4 98 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  98 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 155 (accept_3_2 1 98 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 97 155 (Eq.refl Bool.true) (allA_of_3_0 59 97 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 96 155 (Eq.refl Bool.true) (allA_succ_of_accept 59 96 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 155 (accept_3_2 58 96 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 96 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 57
  96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 155
  (Polychromatic418967fa.accept_13_4_5_12_1_751 56 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 155 (accept_3_2 55 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  96 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 155 (accept_3_2 52 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 155 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 155 (accept_3_2 49 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 155 (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 155 (accept_3_2 46 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 155 (accept_3_2 43 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 155 (accept_3_2 40 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 155 (accept_3_2 37 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 155 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 155 (accept_3_2 34 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 155 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 155 (accept_3_2 31 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 155 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 155 (accept_3_2 28 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 155 (accept_3_2 25 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 155 (accept_3_2 22 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 155 (accept_3_2 19 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 155 (accept_3_2 16 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 155 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 155 (accept_3_2 13 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 155 (accept_3_2 10 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 155 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 155 (accept_3_2 7 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 155 (accept_3_2 4 96 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 155 (Polychromatic418967fa.accept_13_2_5_12_1_2043
  2 96 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 155 (accept_3_2 1 96
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 95 155 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 95 155 5 12 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 95 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 155 (accept_3_2 58 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 95 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 95 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 155
  (Polychromatic418967fa.accept_21_14_11_8_1_5272 56 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 155 5 11 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 155 (accept_3_2 52 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 51
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 155 5 10 19 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 155 (accept_3_2 49
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 155
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 155 (accept_3_2 46 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 155 5 9 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 95 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 155 (accept_3_2 43 95 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 155
  (Polychromatic418967fa.accept_13_2_4_12_1_745 41 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 155 5 8 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 155 (accept_3_2 37 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 155 5 7 19 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 155 (accept_3_2 34
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 155 (Polychromatic418967fa.accept_14_4_11_1_1_940 32 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 155 (accept_3_2 31 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 155 5 6 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 155 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 95 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 155 (accept_3_2 28 95 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 155 (Polychromatic418967fa.accept_24_3_23_11_1_8429 27 95 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 155 5 5 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 155 (Polychromatic418967fa.accept_16_7_15_11_1_951 23 95
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 155 (accept_3_2 22 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 155 5 4 19 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 155 (accept_3_2 19
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 155
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 155 (accept_3_2 16 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 155 5 3 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 155 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 95 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 155 (accept_3_2 13 95 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 155
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 155 5 2 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 155 (Polychromatic418967fa.accept_23_9_3_17_1_8428 9 95 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 155 (accept_3_2 7 95 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 155 5 1 19 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 155 (accept_3_2 4 95
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 155 (Polychromatic418967fa.accept_7_3_4_1_1_71
  3 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 155
  (Polychromatic418967fa.accept_13_2_4_12_1_745 2 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 155 (accept_3_2 1 95 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 94 155 (Eq.refl Bool.true)
  (allA_of_3_0 62 94 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 93 155 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 93 155 31 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 93 155 (accept_3_2 61 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 155 (accept_3_2 58 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 155 (accept_3_2 55 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 155 (accept_3_2 52 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 155 (accept_3_2 49 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 155 (accept_3_2 46 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 155 (accept_3_2 43 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 155 (accept_3_2 40 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 155 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 155 (accept_3_2 37 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 155 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 155 (accept_3_2 34 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 31 93 155 31 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 30 93 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 155 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 93
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 155 (accept_3_2 28 93 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 155 (accept_3_2 25 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 155 (accept_3_2 22 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 155 (accept_3_2 19 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 155 (accept_3_2 16 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 155 (accept_3_2 13 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 155 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 155 (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 155 (accept_3_2 10 93 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 93 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 155 (accept_3_2 7 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 155 (accept_3_2 4 93 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 155 (accept_3_2 1 93 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 92 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 92 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 92 155 (accept_3_2 61 92 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 92 155 (Polychromatic418967fa.accept_13_8_1_12_1_762
  60 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 92 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 92 155 (accept_3_2 58 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 92 155 (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 92 155 (accept_3_2 55 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 92 155 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 92
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 92 155
  (Polychromatic418967fa.accept_10_3_2_5_1_295 53 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 92 155 (accept_3_2 52 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 92 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 92 155 (accept_3_2 49 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 92 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 92 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 92 155 (accept_3_2 46 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 92 155 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 92 155 (accept_3_2 43 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 92 155 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 155
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 92 155 (accept_3_2 40 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 92 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 155 (accept_3_2 37 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 92 155 (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 155
  (Polychromatic418967fa.accept_14_7_8_1_1_1621 35 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 92 155 (accept_3_2 34 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 92 155 (Polychromatic418967fa.accept_17_15_7_2_1_2303 32 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 92 155 (accept_3_2 31 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 92 155 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 92 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 92 155 (accept_3_2 28 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 92 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 155 (accept_3_2 25 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 155 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 92 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 92 155 (accept_3_2 22 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 92 155 (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 155 (accept_3_2 19 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 92 155
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 92 155 (accept_3_2 16 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 92 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 155 (accept_3_2 13 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 155 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 155
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 92 155 (accept_3_2 10 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  92 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 92 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 155 (accept_3_2 7 92 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 155 (Polychromatic418967fa.accept_19_6_16_3_1_1801 6 92 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 155
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 155 (accept_3_2 4 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 92 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 155 (accept_3_2 1 92 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 91 155
  (Eq.refl Bool.true) (allA_of_3_0 65 91 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 90 155 (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 90 155 5 13 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 90 155 (accept_3_2 64 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 90 155 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 155 (Polychromatic418967fa.accept_19_5_14_3_1_4187 62 90
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 155 (accept_3_2 61 90 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 155 5 12 18 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 155
  (Polychromatic418967fa.accept_20_19_10_15_1_1529 59 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 155 (accept_3_2 58 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 155 (Polychromatic418967fa.accept_19_18_14_3_1_8427 56 90
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 155 5 11 18 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 90 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 155 (accept_3_2 52 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 90 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 155 5 10 18 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 155 (accept_3_2 49 90 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 155 (Polychromatic418967fa.accept_17_14_5_2_1_4559 48 90
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 155 (accept_3_2 46 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90
  155 5 9 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  90 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 90 155 (accept_3_2 43 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 90 155 (Polychromatic418967fa.accept_20_2_10_15_1_3953 42 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 155 5 8 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 155
  (Polychromatic418967fa.accept_20_19_10_15_1_1529 39 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 155 (Polychromatic418967fa.accept_20_18_10_15_1_3937 38 90 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 155 (accept_3_2 37 90 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 155 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 90 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 90 155 5 7 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 155 (accept_3_2 34 90 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 155
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 155 (accept_3_2 31 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  155 5 6 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 90 155 (accept_3_2 28 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 155 (Polychromatic418967fa.accept_19_8_14_3_1_4151 27 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 90 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 155 5 5 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 90 155
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 24 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 155 (accept_3_2 22 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 155 5 4 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 155 (accept_3_2 19 90 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 155 (Polychromatic418967fa.accept_19_18_14_3_1_8427 18 90 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 155 (accept_3_2 16 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90
  155 5 3 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  90 155 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 90 155 (accept_3_2 13 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 155 (Polychromatic418967fa.accept_19_11_14_3_1_8426 11 90
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 155 5 2 18 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 155 (Polychromatic418967fa.accept_19_8_14_3_1_4151 8 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 155 (accept_3_2 7 90 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 155 (Polychromatic418967fa.accept_20_6_10_15_1_6879 6 90 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 90 155 5 1 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 155 (accept_3_2 4 90 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 155 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 90 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 155 (accept_3_2 1 90 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 89 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 155 (Polychromatic418967fa.accept_19_8_13_3_1_4172 65 89
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 155 (accept_3_2 64 89 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 89 155 (Polychromatic418967fa.accept_17_12_4_2_1_7116
  63 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 89 155 (accept_3_2 61 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 155 (accept_3_2 58 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 155
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 155 (accept_3_2 55 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 155 (accept_3_2 52 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 155 (accept_3_2 49 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 155 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 155 (accept_3_2 46 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 89 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 155
  (Polychromatic418967fa.accept_10_4_9_5_1_84 44 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 155 (accept_3_2 43 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 155 (accept_3_2 40 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 155 (accept_3_2 37 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 155 (Polychromatic418967fa.accept_19_16_13_3_1_5544 35 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 155 (accept_3_2 34 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 155 (accept_3_2 31 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 155 (Polychromatic418967fa.accept_17_12_4_2_1_7116 29 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 155 (accept_3_2 28 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 89 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 155 (accept_3_2 25 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 155 (accept_3_2 22 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 155 (accept_3_2 19 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 155 (accept_3_2 16 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 155 (accept_3_2 13 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 155 (accept_3_2 10 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 155 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 89 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 155
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 155 (accept_3_2 7 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 155 (accept_3_2 4 89 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 155 (accept_3_2 1 89 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 88 155 (Eq.refl Bool.true)
  (allA_of_3_0 68 88 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 87 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 155 (accept_3_2 67 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 65
  87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 155 (accept_3_2 64 87
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 155
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 155 (accept_3_2 61 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 59
  87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 155 (accept_3_2 58 87
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 155
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 155 (accept_3_2 55 87 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 155 (accept_3_2 52 87
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 155 (Polychromatic418967fa.accept_7_2_3_1_1_10
  51 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 155 (accept_3_2 49 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 155 (accept_3_2 46 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 155 (accept_3_2 43 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 155 (accept_3_2 40 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 155 (accept_3_2 37 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 155 (accept_3_2 34 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 155 (accept_3_2 31 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 155 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 155 (accept_3_2 28 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 155 (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 87
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 155 (accept_3_2 25 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 155 (accept_3_2 22 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 155 (accept_3_2 19 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 155 (accept_3_2 16 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 155 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 155 (accept_3_2 13 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 155 (accept_3_2 10 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 155 (accept_3_2 7 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  155 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 87 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 155 (accept_3_2 4 87 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 155 (accept_3_2 1 87 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 86 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 86 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 86 155 (accept_3_2 67 86 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 86 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 66
  86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 86 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 86 155 (accept_3_2 64 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 86 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 86 155 (accept_3_2 61 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 86 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 86 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 86 155 (accept_3_2 58 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 86 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 86 155 (accept_3_2 55 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 86 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 86 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 86 155 (accept_3_2 52 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 86 155 (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 86 155 (accept_3_2 49 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 86 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 86 155
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 86 155 (accept_3_2 46 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 86 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 86 155 (accept_3_2 43 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 86 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 86 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 86 155 (accept_3_2 40 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 86 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 155 (accept_3_2 37 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 86 155 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 86 155 (accept_3_2 34 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 86 155 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 155 (accept_3_2 31 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 86 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 86 155 (accept_3_2 28 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 86 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 155 (accept_3_2 25 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 86 155
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 86 155 (accept_3_2 22 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 86 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 155 (accept_3_2 19 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 155 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 86 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 86 155 (accept_3_2 16 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 86 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 155 (accept_3_2 13 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 155
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 86 155 (accept_3_2 10 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 86 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 155 (accept_3_2 7 86 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 86 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 86 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 155 (accept_3_2 4 86 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 155
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 155 (accept_3_2 1 86 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 85 155 (Eq.refl Bool.true)
  (allA_of_3_0 71 85 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 84 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 84 155 (accept_3_2 70 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 68
  84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 155 (accept_3_2 67 84
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 155
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 155 (Polychromatic418967fa.accept_17_14_16_2_1_4553 65 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 155 (accept_3_2 64 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 62
  84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 155 (accept_3_2 61 84
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 155
  (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 155 (accept_3_2 58 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 155 (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 155
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 84 155 (accept_3_2 55 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  84 155 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 84 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 155 (accept_3_2 52 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 155 (accept_3_2 49 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  84 155 (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 155 (accept_3_2 46 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 155 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 155 (accept_3_2 43 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  84 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 84 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 155 (accept_3_2 40 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 155
  (Polychromatic418967fa.accept_16_6_4_11_1_1719 38 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 155 (accept_3_2 37 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 155 (accept_3_2 34 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 155 (accept_3_2 31 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  84 155 (Polychromatic418967fa.accept_19_11_8_3_1_862 30 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 84 155 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 155 (accept_3_2 28 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 155 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 155 (accept_3_2 25 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 155 (accept_3_2 22 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 155
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 155 (accept_3_2 19 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  84 155 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 84 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 155 (accept_3_2 16 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 155 (accept_3_2 13 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  84 155 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 84 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 155 (accept_3_2 10 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 155 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 155 (accept_3_2 7 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84
  155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 155 (accept_3_2 4 84 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 155 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 84 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 155 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  2 84 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 155 (accept_3_2 1 84
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 83 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 155 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 83 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 155 (accept_3_2 70 83 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 83 155 (Polychromatic418967fa.accept_13_4_5_12_1_751
  69 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 155 (accept_3_2 67 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 155 (Polychromatic418967fa.accept_13_1_5_12_1_306 66 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 155 (accept_3_2 64 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 155 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 155
  (Polychromatic418967fa.accept_10_2_3_5_1_996 62 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 155 (accept_3_2 61 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 155 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 155 (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 155 (accept_3_2 58 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 83 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 155
  (Polychromatic418967fa.accept_13_4_5_12_1_751 56 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 155 (accept_3_2 55 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 155 (Polychromatic418967fa.accept_13_1_5_12_1_306 53 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 155 (accept_3_2 52 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 155
  (Polychromatic418967fa.accept_19_12_7_3_1_5494 50 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 155 (accept_3_2 49 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 155 (accept_3_2 46 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 155 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 155 (accept_3_2 43 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 155 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 155 (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 155 (accept_3_2 40 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 155 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 83
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 155
  (Polychromatic418967fa.accept_10_8_3_5_1_613 38 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 155 (accept_3_2 37 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 155 (Polychromatic418967fa.accept_25_11_8_5_1_4696 36 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 155 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 155 (accept_3_2 34 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 155
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 155 (accept_3_2 31 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 155 (accept_3_2 28 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 155 (accept_3_2 25 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 155 (Polychromatic418967fa.accept_16_8_3_11_1_4763 24 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 155 (accept_3_2 22 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 155 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 155
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 155 (accept_3_2 19 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 155 (accept_3_2 16 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 155 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 155
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 155 (accept_3_2 13 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 155 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 155 (accept_3_2 10 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 155
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 155 (accept_3_2 7 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  155 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 155 (accept_3_2 4 83 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 155 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 83 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 155 (accept_3_2 1 83 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 82 155 (Eq.refl Bool.true)
  (allA_of_3_0 74 82 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 81 155 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 155 (accept_3_2 73 81 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 155
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 155 (accept_3_2 70 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 155 (accept_3_2 67 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 155
  (Polychromatic418967fa.accept_19_8_5_3_1_4181 65 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 155 (accept_3_2 64 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 155 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 155 (accept_3_2 61 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 155 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 155 (accept_3_2 58 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 155 (accept_3_2 55 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 155
  (Polychromatic418967fa.accept_21_11_18_8_1_5264 53 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 155 (accept_3_2 52 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 155 (accept_3_2 49 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 155 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 155 (accept_3_2 46 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 155 (accept_3_2 43 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 155
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 155 (accept_3_2 40 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 155 (accept_3_2 37 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 155
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 155 (accept_3_2 34 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 155 (accept_3_2 31 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 155
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 155 (accept_3_2 28 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 155 (accept_3_2 25 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 155
  (Polychromatic418967fa.accept_17_6_13_2_1_4549 23 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 155 (accept_3_2 22 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 155 (Polychromatic418967fa.accept_19_2_5_3_1_5536 21 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 155 (accept_3_2 19 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 155 (accept_3_2 16 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 155 (accept_3_2 13 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 155
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 155 (accept_3_2 10 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 155 (accept_3_2 7 81 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 155 (accept_3_2 4 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 155 (accept_3_2 1 81 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76
  80 155 (Eq.refl Bool.true) (allA_succ_of_gcd 75 80 155 5 15 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 155 (accept_3_2 73 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 155
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 155 5 14 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 155 (accept_3_2 67 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 66
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 155 5 13 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 155 (accept_3_2 64
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 155
  (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 155 (accept_3_2 61 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 80 155 5 12 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 80 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 155 (accept_3_2 58 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 155
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 80 155 5 11 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 80 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 155 (accept_3_2 52 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 155 5 10 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 155 (accept_3_2 49
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 155
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 155 (accept_3_2 46 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 80 155 5 9 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 80 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 155 (accept_3_2 43 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 155 5 8 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 155 (accept_3_2 37 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 155
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 80 155 5 7 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 80 155 (accept_3_2 34 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 80 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 155 (accept_3_2 31 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 155 5 6 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 80 155 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 155 (accept_3_2 28 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 155 5 5 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 155 (accept_3_2 22 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 155 5 4 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 155 (accept_3_2 19
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 155 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 155 (accept_3_2 16 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 155 5 3 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 155 (accept_3_2 13 80 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 155 5 2 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 155 (Polychromatic418967fa.accept_19_8_4_3_1_5559 8 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 155 (accept_3_2 7 80 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 155 5 1 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 155 (accept_3_2 4 80
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 155 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 155 (accept_3_2 1 80 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 79 155 (Eq.refl
  Bool.true) (allA_of_3_0 77 79 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 155 (allA_succ_of_accept 77
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 78 155 (accept_3_2 76 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 78 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 155 (Polychromatic418967fa.accept_19_17_2_3_1_4190 74 78
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 155 (accept_3_2 73 78 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 155 (Polychromatic418967fa.accept_10_2_8_5_1_587
  72 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 155 (accept_3_2 70 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 155 (accept_3_2 67 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 155 (accept_3_2 64 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 155 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 155 (accept_3_2 61 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 155 (Polychromatic418967fa.accept_21_18_15_8_1_8425 60 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 155 (accept_3_2 58 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 155 (Polychromatic418967fa.accept_19_18_2_3_1_4177 56 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 155 (accept_3_2 55 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 78 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 155 (accept_3_2 52 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 155 (Polychromatic418967fa.accept_14_9_8_1_1_2381 51 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 155 (accept_3_2 49 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 155
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 155 (accept_3_2 46 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 155 (accept_3_2 43 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 155 (accept_3_2 40 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 155 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 155 (accept_3_2 37 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 155 (accept_3_2 34 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 155 (accept_3_2 31 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 155 (accept_3_2 28 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 155 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 155 (accept_3_2 25 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 155 (accept_3_2 22 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 155 (Polychromatic418967fa.accept_19_1_2_3_1_6995 20 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 155 (accept_3_2 19 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 155 (Polychromatic418967fa.accept_19_18_2_3_1_4177 18 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 155 (accept_3_2 16 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 155 (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 155 (accept_3_2 13 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 155
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 11 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 155 (accept_3_2 10 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 155 (accept_3_2 7 78 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 78 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 155 (accept_3_2 4 78 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 155
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 155 (accept_3_2 1 78 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 155
  (allA_succ_of_accept 76 77 155 (accept_3_2 76 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 155 (accept_3_2 73 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 155 (accept_3_2 70 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 155 (accept_3_2 67 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 155
  (Polychromatic418967fa.accept_20_5_17_15_1_6858 65 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 155 (accept_3_2 64 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 155 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 155 (accept_3_2 61 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 155 (accept_3_2 58 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 155 (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 155 (accept_3_2 55 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 155 (accept_3_2 52 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 155 (accept_3_2 49 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 155
  (Polychromatic418967fa.accept_21_5_14_8_1_6818 47 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 155 (accept_3_2 46 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 155 (Polychromatic418967fa.accept_17_11_9_2_1_8423 45 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 155 (accept_3_2 43 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 155
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 155 (accept_3_2 40 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 155 (accept_3_2 37 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 155 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 155 (accept_3_2 34 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 155 (accept_3_2 31 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 155 (accept_3_2 28 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 155 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 155 (accept_3_2 25 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 155
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 155 (accept_3_2 22 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 155 (Polychromatic418967fa.accept_14_6_7_1_1_78 20 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 155 (accept_3_2 19 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 155 (accept_3_2 16 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 155 (accept_3_2 13 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 155
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 155 (accept_3_2 10 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 155 (Polychromatic418967fa.accept_23_9_8_17_1_8422 9 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 155 (accept_3_2 7 77 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 155
  (Polychromatic418967fa.accept_19_5_1_3_1_8421 5 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 155 (accept_3_2 4 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  155 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 155 (accept_3_2 1 77 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 155 (allA_of_3_0 76 76 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 155 (allA_succ_of_accept 74 75
  155 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 155 (accept_3_2 73 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 155 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 75 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 155 5 14 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 155 (accept_3_2 67 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 75 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 155 5 13 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 155 (accept_3_2 64 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 155 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 75
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 155 (accept_3_2 61 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  155 5 12 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 155 (accept_3_2 58 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 155 5 11 15 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 155
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 155 (accept_3_2 52 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 155 5 10 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 155 (accept_3_2 49 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 155
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 155 (accept_3_2 46 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  155 5 9 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 155 (accept_3_2 43 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 155 5 8 15 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 155 (accept_3_2 37 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 155 (Polychromatic418967fa.accept_21_15_12_8_1_5275 36 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 155 5 7 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 155 (accept_3_2 34 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 155 (accept_3_2 31 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  155 5 6 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 155 (Polychromatic418967fa.accept_17_12_7_2_1_4561 29 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 155 (accept_3_2 28 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 155 5 5 15 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 155 (accept_3_2 22 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 155 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 155 5 4 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 155 (accept_3_2 19 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 155 (accept_3_2 16 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  155 5 3 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 155 (accept_3_2 13 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 155 (Polychromatic418967fa.accept_17_12_7_2_1_4561 12 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 155 5 2 15 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 155
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 155 (accept_3_2 7 75 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 155 5 1 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 155 (accept_3_2 4 75 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 155 (accept_3_2 1 75 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 155 (allA_succ_of_accept
  73 74 155 (accept_3_2 73 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 155
  (Polychromatic418967fa.accept_17_4_6_2_1_5871 72 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 74 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 155 (accept_3_2 70 74 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 68
  74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 155 (accept_3_2 67 74
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 155 (Polychromatic418967fa.accept_7_3_4_1_1_71
  66 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 74 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 74 155 (accept_3_2 64 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 74 155 (Polychromatic418967fa.accept_13_10_9_12_1_2814 62 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 155 (accept_3_2 61 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 155 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 74
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 74 155 (accept_3_2 58 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 74 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 155 (accept_3_2 55 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 74 155 (accept_3_2 52 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 74 155 (Polychromatic418967fa.accept_18_14_2_11_1_4384 50 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 155 (accept_3_2 49 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 155 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 74 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 74 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 74 155 (accept_3_2 46 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 74 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 155 (accept_3_2 43 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 155 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 74 155 (accept_3_2 40 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 74 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 155 (accept_3_2 37 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 155
  (Polychromatic418967fa.accept_17_1_6_2_1_623 35 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 74 155 (accept_3_2 34 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 155 (accept_3_2 31 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 155 (Polychromatic418967fa.accept_17_13_6_2_1_5850 30 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 155 (accept_3_2 28 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 155 (accept_3_2 25 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 155
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 155 (accept_3_2 22 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 155 (accept_3_2 19 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 155 (Polychromatic418967fa.accept_17_1_6_2_1_623 18 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 155 (accept_3_2 16 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 155 (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 155 (accept_3_2 13 74 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 74 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 155
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 155 (accept_3_2 10 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 74 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 74 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 155 (accept_3_2 7 74 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 74 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 74 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 155 (accept_3_2 4 74 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 155
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 155 (accept_3_2 1 74 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 155 (allA_of_3_0 73 73 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 155 (allA_succ_of_accept 71 72 155
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 155 (accept_3_2 70 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 155 (accept_3_2 67 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 155
  (Polychromatic418967fa.accept_19_8_15_3_1_5546 65 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 155 (accept_3_2 64 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 155 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 155 (accept_3_2 61 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 155 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 155 (accept_3_2 58 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 155 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 155 (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 155 (accept_3_2 55 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 54 72
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 155
  (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 155 (accept_3_2 52 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 155 (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 155 (accept_3_2 49 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 155
  (Polychromatic418967fa.accept_10_7_2_5_1_298 47 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 155 (accept_3_2 46 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 155 (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 155 (accept_3_2 43 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 155 (Polychromatic418967fa.accept_25_17_22_5_1_8420 42 72
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 155
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 155 (accept_3_2 40 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 155 (accept_3_2 37 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 155 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 155
  (Polychromatic418967fa.accept_16_3_8_11_1_2714 35 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 155 (accept_3_2 34 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 155 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 155 (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 155 (accept_3_2 31 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 155 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 72
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 155
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 155 (accept_3_2 28 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 155 (Polychromatic418967fa.accept_17_9_4_2_1_2298 26 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 155 (accept_3_2 25 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 155
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 155 (accept_3_2 22 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 155 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 155 (accept_3_2 19 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 155 (accept_3_2 16 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 155 (Polychromatic418967fa.accept_17_15_4_2_1_8419 15 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 155 (Polychromatic418967fa.accept_23_14_3_17_1_8418 14 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 155 (accept_3_2 13 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 155 (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 72
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 155
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 155 (accept_3_2 10 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 155 (accept_3_2 7 72 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 155
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 155 (accept_3_2 4 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 155 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 72 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 155 (accept_3_2 1 72 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 155
  (allA_succ_of_accept 70 71 155 (accept_3_2 70 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 155 (accept_3_2 67 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 155
  (Polychromatic418967fa.accept_17_14_3_2_1_5848 65 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 155 (accept_3_2 64 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 155 (Polychromatic418967fa.accept_16_15_7_11_1_3760 63 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 155 (Polychromatic418967fa.accept_13_10_6_12_1_2780 62 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 155 (accept_3_2 61 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 71 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 155 (accept_3_2 58 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 155 (accept_3_2 55 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 155 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 155
  (Polychromatic418967fa.accept_15_8_11_5_1_169 53 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 155 (accept_3_2 52 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 155 (accept_3_2 49 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 155
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 155 (accept_3_2 46 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 155 (Polychromatic418967fa.accept_17_11_3_2_1_5867 45 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 155 (accept_3_2 43 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 155 (accept_3_2 40 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 38 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 155 (accept_3_2 37 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 155
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 155 (accept_3_2 34 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 155 (accept_3_2 31 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 155
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 155 (accept_3_2 28 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 155 (Polychromatic418967fa.accept_19_8_14_3_1_4151 27 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 155 (accept_3_2 25 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 155 (accept_3_2 22 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 155 (accept_3_2 19 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 155 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 155
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 155 (accept_3_2 16 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 155 (accept_3_2 13 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 155
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 11 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 155 (accept_3_2 10 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 155 (accept_3_2 7 71 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 155 (accept_3_2 4 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  155 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 71 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 155 (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 71 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 155 (accept_3_2 1 71 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 155
  (allA_of_3_0 70 70 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 155 (allA_succ_of_accept 68 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 155 (accept_3_2 67 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 155 (accept_3_2 64 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 155 (accept_3_2 61 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 155 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 155 (accept_3_2 58 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 155 (accept_3_2 55 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 155 (accept_3_2 52 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 155 (accept_3_2 49 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 155 (accept_3_2 46 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 155 (Polychromatic418967fa.accept_18_9_15_11_1_5693 45 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 155 (accept_3_2 43 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 155 (accept_3_2 40 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 155 (accept_3_2 37 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 155 (accept_3_2 34 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 155 (accept_3_2 31 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 155 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 155 (accept_3_2 28 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 155 (accept_3_2 25 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 155 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 155 (accept_3_2 22 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 155 (accept_3_2 19 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 155 (accept_3_2 16 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 155 (accept_3_2 13 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 155 (accept_3_2 10 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 155 (accept_3_2 7 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 155 (accept_3_2 4 69 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 155 (accept_3_2 1 69 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 155 (allA_succ_of_accept 67 68
  155 (accept_3_2 67 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 155 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 155 (accept_3_2 64 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 62
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 155 (accept_3_2 61 68
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 155 (accept_3_2 58 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 155 (Polychromatic418967fa.accept_13_4_3_12_1_2066
  56 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 155 (accept_3_2 55
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 155
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 155 (accept_3_2 52 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 155 (Polychromatic418967fa.accept_12_2_8_11_1_31
  50 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 155 (accept_3_2 49
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 155 (accept_3_2 46 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 155 (accept_3_2 43 68
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 155
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 155 (accept_3_2 40 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 155 (accept_3_2 37 68
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 155
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 155 (accept_3_2 34 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 155 (accept_3_2 31 68
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 155 (Polychromatic418967fa.accept_9_3_5_2_1_28
  30 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 155
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 155 (accept_3_2 28 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 155 (accept_3_2 25 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 155 (accept_3_2 22 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 155 (accept_3_2 19 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 68 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 155 (accept_3_2 16 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 155 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 155 (accept_3_2 13 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 155 (accept_3_2 10 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 155 (accept_3_2 7 68 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 68 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 155
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 155 (accept_3_2 4 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 155 (accept_3_2 1 68 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 155
  (allA_of_3_0 67 67 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 155 (allA_succ_of_accept 65 66 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 155 (accept_3_2 64 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 155 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 155 (accept_3_2 61 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 155 (accept_3_2 58 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 155 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 155 (accept_3_2 55 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 155 (accept_3_2 52 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 155 (accept_3_2 49 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 155 (accept_3_2 46 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 155 (accept_3_2 43 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 155 (accept_3_2 40 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 155 (Polychromatic418967fa.accept_16_6_2_11_1_7132 38 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 155 (accept_3_2 37 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 155 (Polychromatic418967fa.accept_21_15_3_8_1_6822 36 66
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 155 (accept_3_2 34 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 155 (accept_3_2 31 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 155 (accept_3_2 28 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 155 (accept_3_2 25 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 155 (accept_3_2 22 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 155 (Polychromatic418967fa.accept_26_20_14_25_1_8417 20 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 155 (accept_3_2 19 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 155 (accept_3_2 16 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 155 (accept_3_2 13 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 155 (accept_3_2 10 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 66 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 155 (accept_3_2 7 66 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 155 (accept_3_2 4 66 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3
  66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 155 (accept_3_2 1 66 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 155 (allA_succ_of_accept 64 65 155
  (accept_3_2 64 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 155
  (Polychromatic418967fa.accept_16_15_1_11_1_3747 63 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 155 (accept_3_2 61 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 65 155 5 12 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 65 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 155 (accept_3_2 58 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 65
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 155
  (Polychromatic418967fa.accept_17_5_14_2_1_4568 56 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 155 5 11 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 155 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 155 (accept_3_2 52 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 155 (Polychromatic418967fa.accept_19_13_8_3_1_2906
  51 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 155 5 10 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 155 (accept_3_2 49
  65 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 155
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 155 (Polychromatic418967fa.accept_16_15_1_11_1_3747 47 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 155 (accept_3_2 46 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 155 5 9 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 155 (Polychromatic418967fa.accept_16_12_1_11_1_5958 44 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 155 (accept_3_2 43 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 155
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 155 5 8 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 155 (Polychromatic418967fa.accept_17_5_14_2_1_4568 39 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 155 (accept_3_2 37 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 155 (Polychromatic418967fa.accept_14_8_9_1_1_3313
  36 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 155 5 7 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 155 (accept_3_2 34
  65 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 155
  (Polychromatic418967fa.accept_17_16_14_2_1_5841 33 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 155 (Polychromatic418967fa.accept_19_13_8_3_1_2906 32 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 155 (accept_3_2 31 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 155 5 6 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 155 (Polychromatic418967fa.accept_20_9_5_15_1_3965 29 65 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 155 (accept_3_2 28 65 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 155 5 5 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 155 (Polychromatic418967fa.accept_19_4_8_3_1_8416 23 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 155 (accept_3_2 22 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 155 (Polychromatic418967fa.accept_20_1_5_15_1_6913
  21 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 155 5 4 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 155 (accept_3_2 19
  65 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 155 (accept_3_2 16 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 155 5 3 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 155 (accept_3_2 13 65 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 155 (Polychromatic418967fa.accept_16_12_1_11_1_5958 12 65 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 155
  (Polychromatic418967fa.accept_19_11_8_3_1_862 11 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 155 5 2 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 155 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 65 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 155 (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 155 (accept_3_2 7 65 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 155 5 1 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 155 (accept_3_2 4 65
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 155 (Polychromatic418967fa.accept_7_3_2_1_1_225
  3 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 155 (accept_3_2 1 65 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 155 (allA_of_3_0 64 64 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 155 (allA_succ_of_accept 62 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 155 (accept_3_2 61 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 155 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 155 (accept_3_2 58 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 155 (accept_3_2 55 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 155 (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 155 (accept_3_2 52 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 155 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 63 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 155 (accept_3_2 49 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 155 (accept_3_2 46 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 155 (accept_3_2 43 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 155 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 155 (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 155 (accept_3_2 40 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 155 (accept_3_2 37 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 155 (Polychromatic418967fa.accept_16_3_15_11_1_2676 35 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 155 (accept_3_2 34 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 155 (accept_3_2 31 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 155 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 155 (Polychromatic418967fa.accept_20_9_3_15_1_3929 29 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 155 (accept_3_2 28 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 155 (accept_3_2 25 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 155 (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 155 (accept_3_2 22 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 155 (accept_3_2 19 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 155 (accept_3_2 16 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 155 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 155 (accept_3_2 13 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 155 (Polychromatic418967fa.accept_22_11_19_1_1_8415 11 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 155 (accept_3_2 10 63 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 155 (accept_3_2 7 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  155 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 63 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 155 (Polychromatic418967fa.accept_19_5_6_3_1_5578 5 63 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 155 (accept_3_2 4 63 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 155 (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 63 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 155 (accept_3_2 1 63 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 155 (allA_succ_of_accept 61 62 155
  (accept_3_2 61 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 155 (accept_3_2 58 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 155 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 155 (accept_3_2 55
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 155 (accept_3_2 52 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 155 (accept_3_2 49 62
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 155
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 155 (accept_3_2 46 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 155 (accept_3_2 43 62
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 155 (accept_3_2 40 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 155 (Polychromatic418967fa.accept_10_8_2_5_1_596
  38 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 155 (accept_3_2 37
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 155
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 155 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 155 (accept_3_2 34 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 31 62 155 31 1 2 5 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 30 62 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 155 (accept_3_2 28 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 26
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 155 (accept_3_2 25 62
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 155 (accept_3_2 22 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 155 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 155 (accept_3_2 19
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 155
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 155 (accept_3_2 16 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 62 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 155 (accept_3_2 13 62
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 62 155 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 155 (accept_3_2 10 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 62 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 8
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 155 (accept_3_2 7 62 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 155 (accept_3_2 4 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 155 (accept_3_2 1 62 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 155
  (allA_of_3_0 61 61 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 155 (allA_succ_of_accept 59 60 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 155 (accept_3_2 58 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 155 (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 155 5 11 12 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 155 (accept_3_2 52 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 155 (Polychromatic418967fa.accept_18_15_6_11_1_5651 51 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 155 5 10 12 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 155 (accept_3_2 49 60 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 48
  60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 155 (accept_3_2 46 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60
  155 5 9 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  60 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 155 (accept_3_2 43 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 155 (Polychromatic418967fa.accept_16_10_12_11_1_346 42 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 155 5 8 12 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 155 (accept_3_2 37 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 155 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 155 5 7 12 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 155 (accept_3_2 34 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 155 (accept_3_2 31 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  155 5 6 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 155 (Polychromatic418967fa.accept_22_7_16_1_1_8414 29 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 155 (accept_3_2 28 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 155 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 155 5 5 12 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 155 (accept_3_2 22 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 155 5 4 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 155 (accept_3_2 19 60 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 155 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 155 (accept_3_2 16 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60
  155 5 3 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  60 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 155 (accept_3_2 13 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 155 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 60
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 155 5 2 12 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 155
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 155 (accept_3_2 7 60 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 60 155 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 60 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 155 5 1 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 155 (accept_3_2 4 60 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 155
  (Polychromatic418967fa.accept_25_2_10_5_1_8413 2 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 155 (accept_3_2 1 60 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 155 (allA_succ_of_accept 58 59 155
  (accept_3_2 58 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 155
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 59 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 155 (accept_3_2 55 59 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 155 (accept_3_2 52 59
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 155 (Polychromatic418967fa.accept_7_2_3_1_1_10
  51 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 155
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 155 (accept_3_2 49 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 155 (accept_3_2 46 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 155 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 155 (accept_3_2 43 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 155 (accept_3_2 40 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 155
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 38 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 155 (accept_3_2 37 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 155 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 155 (accept_3_2 34 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 155 (accept_3_2 31 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 155 (Polychromatic418967fa.accept_23_6_13_17_1_8412 29 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 155 (accept_3_2 28 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 155 (Polychromatic418967fa.accept_17_10_8_2_1_8411 27 59
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 155 (accept_3_2 25 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 155 (accept_3_2 22 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 155
  (Polychromatic418967fa.accept_19_1_2_3_1_6995 20 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 155 (accept_3_2 19 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 155 (accept_3_2 16 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 155
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 155 (accept_3_2 13 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 155 (accept_3_2 10 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 155 (accept_3_2 7 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 155 (accept_3_2 4 59 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 155 (accept_3_2 1 59 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 155 (allA_of_3_0 58 58 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 155
  (allA_succ_of_accept 56 57 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 155 (accept_3_2 55 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 53
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 155 (accept_3_2 52 57
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 155
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 155 (accept_3_2 49 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 155 (Polychromatic418967fa.accept_11_3_2_1_1_994
  47 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 155 (accept_3_2 46
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 155
  (Polychromatic418967fa.accept_13_6_5_12_1_307 45 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 155 (accept_3_2 43 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 155 (accept_3_2 40 57
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 155
  (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 155 (accept_3_2 37 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 155 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 155 (accept_3_2 34 57
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 155
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 155 (accept_3_2 31 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 155 (Polychromatic418967fa.accept_17_12_6_2_1_2346
  29 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 155 (accept_3_2 28
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 155
  (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 155 (accept_3_2 25 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 155 (accept_3_2 22 57
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 155
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 155 (accept_3_2 19 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 155 (accept_3_2 16 57
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 155
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 155 (accept_3_2 13 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 155 (Polychromatic418967fa.accept_25_11_7_5_1_8410
  11 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 155 (accept_3_2 10
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 155
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 155 (accept_3_2 7 57 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 57 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 5
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 155 (accept_3_2 4 57 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 155 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 155 (accept_3_2 1 57 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  155))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 155 (allA_succ_of_accept 55 56 155
  (accept_3_2 55 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 155
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 155 (accept_3_2 52 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 155 (Polychromatic418967fa.accept_12_2_8_11_1_31
  50 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 155 (accept_3_2 49
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 155
  (Polychromatic418967fa.accept_17_14_5_2_1_4559 48 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 155 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 155 (accept_3_2 46 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 44
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 155 (accept_3_2 43 56
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 56 155
  (Polychromatic418967fa.accept_13_3_4_12_1_36 42 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 56 155 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 155 (accept_3_2 40 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 155 (Polychromatic418967fa.accept_12_2_8_11_1_31
  38 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 155 (accept_3_2 37
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 155
  (Polychromatic418967fa.accept_15_6_11_5_1_168 36 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 56 155 (Polychromatic418967fa.accept_16_3_8_11_1_2714 35 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 155 (accept_3_2 34 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 155 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  32 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 155 (accept_3_2 31
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 155
  (Polychromatic418967fa.accept_19_11_18_3_1_1755 30 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 56 155 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 155 (accept_3_2 28 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 155 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 155 (accept_3_2 25
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 155
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 155 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 155 (accept_3_2 22 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 155 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  20 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 155 (accept_3_2 19
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 155
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 56 155 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 155 (accept_3_2 16 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 155 (accept_3_2 13 56
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 155
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 155 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 155 (accept_3_2 10 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 155 (Polychromatic418967fa.accept_13_8_4_12_1_2753
  8 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 155 (accept_3_2 7 56
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 155
  (Polychromatic418967fa.accept_15_6_11_5_1_168 6 56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 155 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 155 (accept_3_2 4 56 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 155 (accept_3_2 1 56 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 155))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 155 (allA_of_3_0 55 55 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 155
  (allA_succ_of_accept 53 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 155 (accept_3_2 52 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 155 (Polychromatic418967fa.accept_16_2_6_11_1_1722
  50 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 155 (accept_3_2 49
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 155 (Polychromatic418967fa.accept_21_5_12_8_1_6807 47 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 155 (accept_3_2 46 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 155 (Polychromatic418967fa.accept_13_5_2_12_1_1301
  44 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 155 (accept_3_2 43
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 155
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 155 (accept_3_2 40 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 155 (accept_3_2 37 54
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 155
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 155 (accept_3_2 34 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 155 (accept_3_2 31 54
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 155
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 155 (accept_3_2 28 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 155 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 155 (accept_3_2 25
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 155 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 155 (accept_3_2 22 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 155 (accept_3_2 19 54
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 155 (accept_3_2 16 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 155 (Polychromatic418967fa.accept_19_15_16_3_1_8409 15 54 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 155
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 155 (accept_3_2 13 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 155 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 155 (accept_3_2 10 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 155
  (Polychromatic418967fa.accept_20_8_14_15_1_6932 8 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 155 (accept_3_2 7 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 155 (accept_3_2 4 54 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 54 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 155 (accept_3_2 1 54
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 155))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 155 (allA_succ_of_accept 52 53 155 (accept_3_2 52 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 155 (accept_3_2 49 53 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 48
  53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 155 (accept_3_2 46 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 155 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 155 (accept_3_2 43 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 155 (accept_3_2 40 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 155 (accept_3_2 37 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 155 (Polychromatic418967fa.accept_19_17_15_3_1_4174 36 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 155
  (Polychromatic418967fa.accept_19_16_15_3_1_8408 35 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 155 (accept_3_2 34 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 155 (accept_3_2 31 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 155
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 155 (accept_3_2 28 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 155 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 155 (accept_3_2 25 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 155 (accept_3_2 22 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 155 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 155 (accept_3_2 19 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 155 (accept_3_2 16 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 155 (accept_3_2 13 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 155
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 155 (accept_3_2 10 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 155 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 155 (accept_3_2 7 53 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 155 (accept_3_2 4 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 155 (accept_3_2 1 53 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 155))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 155 (allA_of_3_0 52 52
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 155 (allA_succ_of_accept 50 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 155 (accept_3_2 49 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 155 (Polychromatic418967fa.accept_16_15_3_11_1_5997 47 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 155 (accept_3_2 46 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 155 (accept_3_2 43 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 155 (accept_3_2 40 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 155 (accept_3_2 37 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 155 (accept_3_2 34 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 155 (accept_3_2 31 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 155 (accept_3_2 28 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 155 (accept_3_2 25 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 155 (accept_3_2 22 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 155 (accept_3_2 19 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 155 (accept_3_2 16 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 155 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 155 (accept_3_2 13 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 155 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 155 (accept_3_2 10 51 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 155 (accept_3_2 7 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 155 (accept_3_2 4 51 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 155 (accept_3_2 1 51 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 155)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 155 (allA_succ_of_accept 49 50 155 (accept_3_2 49 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 155 (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 50
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 155 (accept_3_2 46 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 155 5 9 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 50 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 155 (accept_3_2 43 50
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 155
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 155 5 8 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 155
  (Polychromatic418967fa.accept_11_5_6_1_1_988 38 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 155 (accept_3_2 37 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 155 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 155 5 7 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 155 (accept_3_2 34 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 155 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 155 (accept_3_2 31 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 155 5 6 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 155 (accept_3_2 28 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 155 5 5 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 155 (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 50
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 155 (accept_3_2 22 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 155 5 4 10 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 155 (accept_3_2 19
  50 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 155
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 155 (accept_3_2 16 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 155 5 3 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 155 (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 50 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 155 (accept_3_2 13 50 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 155
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 11 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 155 5 2 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 155 (accept_3_2 7 50 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 155 5 1 10 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 155 (accept_3_2 4 50
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 155 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 155
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 155 (accept_3_2 1 50 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  155)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 155 (allA_of_3_0 49 49 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 155 (allA_succ_of_accept 47 48 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 155 (accept_3_2 46 48
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 155
  (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 48 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 155 (accept_3_2 43 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 48 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 155 (accept_3_2 40 48
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 155
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 155 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 155 (accept_3_2 37 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 48 155 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 155 (accept_3_2 34 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 155 (accept_3_2 31 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 155
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 155 (accept_3_2 28 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 155 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 155 (accept_3_2 25 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 155 (accept_3_2 22 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 155 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 155 (Polychromatic418967fa.accept_17_3_14_2_1_646 20 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 155 (accept_3_2 19 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 155 (Polychromatic418967fa.accept_25_18_23_5_1_8406 18 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 155 (accept_3_2 16 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 155 (accept_3_2 13 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 155
  (Polychromatic418967fa.accept_19_11_10_3_1_2934 11 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 155 (accept_3_2 10 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 155 (accept_3_2 7 48 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 155
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 155 (accept_3_2 4 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  155 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 155 (accept_3_2 1 48 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 155)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 155 (allA_succ_of_accept 46
  47 155 (accept_3_2 46 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 155 (accept_3_2 43 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 155 (accept_3_2 40 47
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 155 (accept_3_2 37 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 155 (Polychromatic418967fa.accept_11_2_3_1_1_244
  35 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 155 (accept_3_2 34
  47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 155
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 155 (accept_3_2 31 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 155 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 155
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 155 (accept_3_2 28 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 155 (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 155 (accept_3_2 25 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 155
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 155 (accept_3_2 22 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 155 (Polychromatic418967fa.accept_20_1_7_15_1_1521 21 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 155 (accept_3_2 19 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 155 (accept_3_2 16 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 155 (Polychromatic418967fa.accept_17_15_13_2_1_3418 15 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 155 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 155 (accept_3_2 13 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 155 (accept_3_2 10 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 155 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 155 (accept_3_2 7 47 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 155
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 155 (accept_3_2 4 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 155 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 155 (accept_3_2 1 47 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 155))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 155 (allA_of_3_0 46 46 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 155 (allA_succ_of_accept 44 45 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 155 (accept_3_2 43 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 155 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 155 5 8 9 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 155 (accept_3_2 37 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 155 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 155 5 7 9 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 155 (accept_3_2 34 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 155 (accept_3_2 31 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45
  155 5 6 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  45 155 (Polychromatic418967fa.accept_19_10_7_3_1_6977 29 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 155 (accept_3_2 28 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 155 5 5 9 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 155
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 155 (accept_3_2 22 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 155 (Polychromatic418967fa.accept_20_1_5_15_1_6913 21 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 155 5 4 9 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 155 (accept_3_2 19 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 155
  (Polychromatic418967fa.accept_20_17_5_15_1_6912 17 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 155 (accept_3_2 16 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45
  155 5 3 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 155 (accept_3_2 13 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 155 5 2 9 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 155 (accept_3_2 7 45 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 155 5 1 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 155 (accept_3_2 4 45 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 155 (accept_3_2 1 45 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  155))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 155 (allA_succ_of_accept 43 44 155 (accept_3_2 43 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 155 (accept_3_2 40 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 155 (accept_3_2 37 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 155
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 155 (Polychromatic418967fa.accept_19_16_6_3_1_6972 35 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 155 (accept_3_2 34 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 155 (accept_3_2 31 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 155
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 155 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 155 (accept_3_2 28 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 155 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 155 (accept_3_2 25
  44 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 155
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 155 (accept_3_2 22 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 155 (accept_3_2 19 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 155
  (Polychromatic418967fa.accept_19_18_6_3_1_8405 18 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 155 (accept_3_2 16 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 155 (accept_3_2 13 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 155
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 155 (accept_3_2 10 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 155 (Polychromatic418967fa.accept_13_8_5_12_1_2755
  8 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 155 (accept_3_2 7 44
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 155 (Polychromatic418967fa.accept_7_6_2_1_1_214
  6 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 155 (accept_3_2 4 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 155 (accept_3_2 1 44 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 155)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 155 (allA_of_3_0 43 43 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 155 (allA_succ_of_accept 41 42 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 155 (accept_3_2 40 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 155 (accept_3_2 37 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 155 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 42 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 155 (accept_3_2 34 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 155 (accept_3_2 31 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 155 (accept_3_2 28 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 155 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 155 (accept_3_2 25 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 42 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 155 (accept_3_2 22 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 155 (Polychromatic418967fa.accept_19_1_4_3_1_8404 20 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 155 (accept_3_2 19 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 155 (accept_3_2 16 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 155 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 155 (accept_3_2 13 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 155
  (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 155 (accept_3_2 10 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 155 (accept_3_2 7 42 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 155 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 42 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 155 (accept_3_2 4 42 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 155
  (Polychromatic418967fa.accept_13_2_3_12_1_735 2 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 155 (accept_3_2 1 42 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  155)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 155 (allA_succ_of_accept 40 41 155 (accept_3_2 40 41 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 39
  41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 155 (accept_3_2 37 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 155 (accept_3_2 34 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 155
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 155 (accept_3_2 31 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 155 (accept_3_2 28 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 155 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 155 (accept_3_2 25 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 155 (accept_3_2 22 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 155
  (Polychromatic418967fa.accept_16_4_9_11_1_7159 20 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 155 (accept_3_2 19 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 155 (accept_3_2 16 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 155 (accept_3_2 13 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 155 (Polychromatic418967fa.accept_21_11_20_8_1_8403 11 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 155 (accept_3_2 10 41 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 155
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 155 (accept_3_2 7 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 155 (accept_3_2 4 41 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 155 (accept_3_2 1 41 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 155))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 155
  (allA_of_3_0 40 40 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 155 (allA_succ_of_accept 38 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 155 (accept_3_2 37 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 155 (accept_3_2 34 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 155 (accept_3_2 31 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 155 (Polychromatic418967fa.accept_19_11_1_3_1_5555 30 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 155 (accept_3_2 28 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 155 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 39 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 155 (accept_3_2 25 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 155 (accept_3_2 22 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 155 (accept_3_2 19 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 155 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 155 (accept_3_2 16 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 155 (accept_3_2 13 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 155 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 155 (accept_3_2 10 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 155 (accept_3_2 7 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  155 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 155 (accept_3_2 4 39 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 155 (accept_3_2 1 39 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 155))))))))))))))))))))))))))))))))))))))) (allB_succ 38 155
  (allA_succ_of_accept 37 38 155 (accept_3_2 37 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 155 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 155 (Polychromatic418967fa.accept_16_3_6_11_1_2718 35 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 155 (accept_3_2 34 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 155 (accept_3_2 31 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 155 (accept_3_2 28 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 155 (accept_3_2 25 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 155 (Polychromatic418967fa.accept_21_3_17_8_1_8402 24 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 155 (accept_3_2 22 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 155
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 155 (accept_3_2 19 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 155 (accept_3_2 16 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 155
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 155 (accept_3_2 13 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 155 (accept_3_2 10 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 155
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 155 (accept_3_2 7 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  155 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 38 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 155 (accept_3_2 4 38 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 155 (accept_3_2 1 38 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 155)))))))))))))))))))))))))))))))))))))) (allB_succ 37 155
  (allA_of_3_0 37 37 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 155 (allA_succ_of_accept 35 36 155
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 155 (accept_3_2 34 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 155 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 155 (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 155 (accept_3_2 31 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 155 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 36 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 155
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 155 (accept_3_2 28 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 155 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 155 (accept_3_2 25 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 155
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 155 (accept_3_2 22 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 155 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 155 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 155 (accept_3_2 19 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 36 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 155
  (Polychromatic418967fa.accept_21_17_15_8_1_6799 17 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 155 (accept_3_2 16 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 155 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 155 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 155 (accept_3_2 13 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 155
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 155 (accept_3_2 10 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 155 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 155 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 155 (accept_3_2 7 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 155 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 36 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 155
  (Polychromatic418967fa.accept_19_5_17_3_1_4152 5 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 155 (accept_3_2 4 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  155 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 36 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 155 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 155 (accept_3_2 1 36 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 155)))))))))))))))))))))))))))))))))))) (allB_succ 35 155 (allA_succ_of_accept 34 35
  155 (accept_3_2 34 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 155 (accept_3_2 31 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 155 5 6 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 155 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 35 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 155 (accept_3_2 28 35 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 155 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 35 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 155
  (Polychromatic418967fa.accept_21_5_14_8_1_6818 26 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 155 5 5 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 155 (accept_3_2 22 35 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 21
  35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 155 5 4 7 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 155 (accept_3_2 19
  35 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 155
  (Polychromatic418967fa.accept_19_18_16_3_1_1803 18 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 155 (Polychromatic418967fa.accept_19_17_16_3_1_8401 17 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 155 (accept_3_2 16 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 155 5 3 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 155 (accept_3_2 13 35 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 155
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 155 5 2 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 155 (Polychromatic418967fa.accept_22_9_13_1_1_8400 9 35 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 155 (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 35 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 155 (accept_3_2 7 35 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 155 5 1 7 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 155 (accept_3_2 4 35
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 155 (Polychromatic418967fa.accept_9_3_8_2_1_162
  3 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 155
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 2 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 155 (accept_3_2 1 35 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  155))))))))))))))))))))))))))))))))))) (allB_succ 34 155 (allA_of_3_0 34 34 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 155 (allA_succ_of_accept 32 33 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 155 (accept_3_2 31 33 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 155
  (Polychromatic418967fa.accept_22_7_11_1_1_6711 29 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 155 (accept_3_2 28 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 155 (accept_3_2 25 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 155 (accept_3_2 22 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 155 (accept_3_2 19 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 155
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 155 (accept_3_2 16 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 155 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 155 (accept_3_2 13 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 155
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 155 (accept_3_2 10 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 155 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 155 (accept_3_2 7 33 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 155
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 155 (accept_3_2 4 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 155 (accept_3_2 1 33 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 155))))))))))))))))))))))))))))))))) (allB_succ 32 155 (allA_succ_of_accept 31 32 155
  (accept_3_2 31 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 155
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 155 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 32 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 155 (accept_3_2 28 32 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 26
  32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 155 (accept_3_2 25 32
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 155 (Polychromatic418967fa.accept_7_3_4_1_1_71
  24 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 155
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 155 (accept_3_2 22 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 155 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 155 (accept_3_2 19 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 155 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 155
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 155 (accept_3_2 16 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 155 (accept_3_2 13 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 155
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 155 (accept_3_2 10 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 155 (accept_3_2 7 32 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 32 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 155
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 155 (accept_3_2 4 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 155 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 32 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 155 (accept_3_2 1 32 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 155)))))))))))))))))))))))))))))))) (allB_succ 31 155 (allA_of_3_0 31 31 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 155 (allA_succ_of_accept 29 30 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 155 (accept_3_2 28 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 155 5 5 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 155 (accept_3_2 22 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 30 155 5 4 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 155 (accept_3_2 19 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 30 155 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 30 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 155 (accept_3_2 16 30 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 155 5 3 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 155 (Polychromatic418967fa.accept_9_5_3_2_1_171 14
  30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 155 (accept_3_2 13 30
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 155
  (Polychromatic418967fa.accept_19_12_11_3_1_8399 12 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 155 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 30 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 155 5 2 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 155 (accept_3_2 7 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30
  155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 155 5 1 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 155 (accept_3_2 4 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 155 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 30 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 155 (accept_3_2 1 30 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 155)))))))))))))))))))))))))))))) (allB_succ 29 155 (allA_succ_of_accept 28 29 155
  (accept_3_2 28 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 155
  (Polychromatic418967fa.accept_17_10_12_2_1_3385 27 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 155 (accept_3_2 25 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 155 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 155 (Polychromatic418967fa.accept_15_8_14_5_1_2089
  23 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 155 (accept_3_2 22
  29 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 155
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 155 (Polychromatic418967fa.accept_19_1_10_3_1_8398 20 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 155 (accept_3_2 19 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 155 (Polychromatic418967fa.accept_11_6_7_1_1_564
  17 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 155 (accept_3_2 16
  29 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 155
  (Polychromatic418967fa.accept_13_2_3_12_1_735 15 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 155 (accept_3_2 13 29 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 155 (Polychromatic418967fa.accept_19_12_10_3_1_5503 12 29 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 155
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 155 (accept_3_2 10 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 155 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 155 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 155 (accept_3_2 7 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 155
  (Polychromatic418967fa.accept_19_5_10_3_1_5460 5 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 155 (accept_3_2 4 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  155 (Polychromatic418967fa.accept_20_3_9_15_1_6847 3 29 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 155 (accept_3_2 1 29 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 155))))))))))))))))))))))))))))) (allB_succ 28 155 (allA_of_3_0 28 28 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 27 155 (allA_succ_of_accept 26 27 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 155 (accept_3_2 25 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 155 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 155 (accept_3_2 22 27 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 155 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 155 (accept_3_2 19 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 155 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 155 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 27 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 155 (accept_3_2 16 27 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 155 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 27 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 155 (accept_3_2 13 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 155 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 27 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 155 (accept_3_2 10 27 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 155 (accept_3_2 7 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  155 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 155 (accept_3_2 4 27 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 155 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 155 (accept_3_2 1 27 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 155))))))))))))))))))))))))))) (allB_succ 26 155
  (allA_succ_of_accept 25 26 155 (accept_3_2 25 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 155 (accept_3_2 22 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 155
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 155 (accept_3_2 19 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 155 (accept_3_2 16 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 155
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 155 (accept_3_2 13 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 155 (accept_3_2 10 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 155
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 155 (accept_3_2 7 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 155 (accept_3_2 4 26 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 155 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  2 26 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 155 (accept_3_2 1 26
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 155)))))))))))))))))))))))))) (allB_succ 25 155 (allA_of_3_0
  25 25 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 155 (allA_succ_of_accept 23 24 155
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 155 (accept_3_2 22 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 155 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 24 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 155 (accept_3_2 19 24 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 155
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 155 (accept_3_2 16 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 155 (Polychromatic418967fa.accept_17_15_7_2_1_2303 15 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 155 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 155 (accept_3_2 13 24 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 155
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 155 (accept_3_2 10 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 155 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 24 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 155 (accept_3_2 7 24 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 155 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 155
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 155 (accept_3_2 4 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 155 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 155 (accept_3_2 1 24 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 155)))))))))))))))))))))))) (allB_succ 23 155 (allA_succ_of_accept 22 23 155 (accept_3_2 22
  23 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 155
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 155 (accept_3_2 19 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 155 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 23 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 155 (accept_3_2 16 23
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 155
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 155 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 155 (accept_3_2 13 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 155
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 23 155 (accept_3_2 10 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 23 155 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 155 (accept_3_2 7 23 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 155 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 155
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 5 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 155 (accept_3_2 4 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 155 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 155 (accept_3_2 1 23 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 155))))))))))))))))))))))) (allB_succ 22 155 (allA_of_3_0 22 22 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 155 (allA_succ_of_accept 20 21 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 155 (accept_3_2 19 21 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 155
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 155 (accept_3_2 16 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 155 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 155 (accept_3_2 13 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 155 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 21 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 155
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 155 (accept_3_2 10 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 155 (accept_3_2 7 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 155 (accept_3_2 4 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  155 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 155 (accept_3_2 1 21 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 155))))))))))))))))))))) (allB_succ 20 155 (allA_succ_of_accept 19 20 155
  (accept_3_2 19 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 155
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 155 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 20 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 155 (accept_3_2 16 20 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 155 5 3 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 155 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 20 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 155 (accept_3_2 13 20 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 155 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 20 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 155
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 155 5 2 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 155 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 20 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 155 (accept_3_2 7 20 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 155 (Polychromatic418967fa.accept_13_6_7_12_1_3504
  6 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 155 5 1 4 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 155 (accept_3_2 4 20
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 155 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 155
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 155 (accept_3_2 1 20 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  155)))))))))))))))))))) (allB_succ 19 155 (allA_of_3_0 19 19 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 155 (allA_succ_of_accept 17 18 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 155 (accept_3_2 16 18 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 155 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 18 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 155
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 155 (accept_3_2 13 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 155 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 18 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 155 (accept_3_2 10 18 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 155
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 155 (accept_3_2 7 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  155 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 18 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 155 (accept_3_2 4 18 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 155 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  18 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 155 (accept_3_2 1 18 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 155)))))))))))))))))) (allB_succ 17 155 (allA_succ_of_accept 16
  17 155 (accept_3_2 16 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 155
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 155 (accept_3_2 13 17 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 155 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  17 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 155 (accept_3_2 10 17
  155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 155 (Polychromatic418967fa.accept_7_2_3_1_1_10
  9 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 155
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 155 (accept_3_2 7 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 155 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 155 (accept_3_2 4 17 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 155 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 155 (accept_3_2 1 17 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 155))))))))))))))))) (allB_succ 16 155 (allA_of_3_0 16 16 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 155 (allA_succ_of_accept 14 15 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 155 (accept_3_2 13 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 155 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 155 (Polychromatic418967fa.accept_22_11_15_1_1_8397 11 15 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 155 5 2 3 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 155
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 155 (accept_3_2 7 15 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 155 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 15 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 155 5 1 3 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 155 (accept_3_2 4 15 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 155 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 155
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 155 (accept_3_2 1 15 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  155))))))))))))))) (allB_succ 14 155 (allA_succ_of_accept 13 14 155 (accept_3_2 13 14 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 155 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 155 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  11 14 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 155 (accept_3_2 10
  14 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 155
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 155 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 155 (accept_3_2 7 14 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 155 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 155 (accept_3_2 4 14 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 155
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 14 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 155 (accept_3_2 1 14 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  155)))))))))))))) (allB_succ 13 155 (allA_of_3_0 13 13 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 155
  (allA_succ_of_accept 11 12 155 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 155 (accept_3_2 10 12 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 155 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 12 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 155 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  12 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 155 (accept_3_2 7 12 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 155 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  12 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 155
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 155 (accept_3_2 4 12 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 155 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 12 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 155 (accept_3_2 1 12 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 155)))))))))))) (allB_succ 11 155 (allA_succ_of_accept 10 11 155 (accept_3_2 10 11 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 155 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  11 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 155
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 11 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 155 (accept_3_2 7 11 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  155 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 11 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 11 155 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 11 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 155 (accept_3_2 4 11 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 155 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 155
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 11 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 155 (accept_3_2 1 11 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  155))))))))))) (allB_succ 10 155 (allA_of_3_0 10 10 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 155
  (allA_succ_of_accept 8 9 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 155 (accept_3_2 7 9 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 155 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 155 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 155 (Polychromatic418967fa.accept_16_5_9_11_1_3762 5
  9 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 155 (accept_3_2 4 9 155
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 155 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 155 (accept_3_2 1 9 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 155)))))))))
  (allB_succ 8 155 (allA_succ_of_accept 7 8 155 (accept_3_2 7 8 155 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 155 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 155 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 155 (accept_3_2 4 8 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 155 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 155
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 8 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 155 (accept_3_2 1 8 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 155))))))))
  (allB_succ 7 155 (allA_of_3_0 7 7 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 155 (allA_succ_of_accept 5
  6 155 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 155 (accept_3_2 4 6 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 155
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 155 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 155 (accept_3_2 1 6 155 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 155)))))) (allB_succ 5 155 (allA_succ_of_accept 4 5 155 (accept_3_2 4 5 155 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 155 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 155
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 155
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 155 (accept_3_2 1 5 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 155)))))
  (allB_succ 4 155 (allA_of_3_0 4 4 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 155 (allA_succ_of_accept 2
  3 155 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 155 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 155 (accept_3_2 1 3 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 155)))
  (allB_succ 2 155 (allA_succ_of_accept 1 2 155 (accept_3_2 1 2 155 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  155)) (allB_two
  155)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


