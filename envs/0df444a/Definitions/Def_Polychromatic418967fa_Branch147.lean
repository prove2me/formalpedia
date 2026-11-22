-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch147
-- name    : Polychromatic418967fa_Branch147
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:56.436282+00:00
-- url     : https://prove2.me/theorems/03a7ea1c-9909-47e4-a3bb-f4fdfb77a222
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch147_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_147 : allB 147 147 :=
  allB_succ' 2 146 147 (Eq.refl Bool.true) (allA_succ_of_accept 1 146 147 (accept_3_4 1 146 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 147)) (allB_succ' 3 145 147 (Eq.refl Bool.true) (allA_succ_of_accept 2 145 147
  (accept_3_5 2 145 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 147
  (Polychromatic418967fa.accept_27_1_10_12_1_2166 1 145 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 145 147))) (allB_succ' 4 144 147 (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 147 3 1 48 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 147
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 147 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 144 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 147)))) (allB_succ' 5 143 147 (Eq.refl Bool.true) (allA_succ_of_accept 4
  143 147 (accept_3_4 4 143 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 147
  (Polychromatic418967fa.accept_15_3_8_12_1_900 3 143 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 143 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 147 (accept_3_4 1 143 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 143 147))))) (allB_succ' 6 142 147 (Eq.refl Bool.true) (allA_succ_of_accept 5 142 147
  (accept_3_5 5 142 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 147
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 142 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 142 147 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 142 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 147 (accept_3_5 2 142 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 142 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 147)))))) (allB_succ' 7 141 147 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 141 147 3 2 47 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 141 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 147 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 147 3 1 47 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 147))))))) (allB_succ' 8 140 147 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  140 147 7 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 140 147 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 140 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 147 (accept_3_4 4 140 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 147 (Polychromatic418967fa.accept_19_3_7_14_1_3669 3 140 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 147
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 140 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 147 (accept_3_4 1 140 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  147)))))))) (allB_succ' 9 139 147 (Eq.refl Bool.true) (allA_succ_of_accept 8 139 147 (accept_3_5 8 139 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 147 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 147
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 147 (accept_3_5 5 139 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 147 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 139 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 147 (accept_3_5 2 139 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 147 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 139 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 147))))))))) (allB_succ' 10 138 147 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 138 147 3 3 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 138 147 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 138 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 147 (Polychromatic418967fa.accept_15_7_3_12_1_365
  7 138 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 147 3 2 46 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 147
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 147 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 138 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 147 3 1 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 147 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 138 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 147
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 147)))))))))) (allB_succ' 11 137 147 (Eq.refl Bool.true) (allA_succ_of_accept 10 137 147 (accept_3_4 10
  137 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 147
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 137 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 137 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 147 (accept_3_4 7 137 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 137 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 147 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  137 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 147 (accept_3_4 4 137
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 147
  (Polychromatic418967fa.accept_13_3_7_4_1_435 3 137 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 137 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 147 (accept_3_4 1 137 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 137 147))))))))))) (allB_succ' 12 136 147 (Eq.refl Bool.true) (allA_succ_of_accept 11 136 147
  (accept_3_5 11 136 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 147
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 136 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 136 147 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 136 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 147 (accept_3_5 8 136 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 136 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 147 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  136 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 147 (accept_3_5 5 136
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 147
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 136 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 136 147 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 136 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 147 (accept_3_5 2 136 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 136 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 147)))))))))))) (allB_succ' 13 135 147 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 135 147 3 4 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 135 147 (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 135 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 147 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 135
  147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 147 3 3 45 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 147
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 135 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 147 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 135 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 147 3 2 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 147 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 135 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 147
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 135 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 147 3 1 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 147 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 135 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 147 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 135 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 147))))))))))))) (allB_succ' 14 134 147
  (Eq.refl Bool.true) (allA_succ_of_accept 13 134 147 (accept_3_4 13 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 134 147 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 134 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 147 (accept_3_4 10 134 147
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  134 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 147
  (Polychromatic418967fa.accept_22_8_2_15_1_6041 8 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 147 (accept_3_4 7 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 147 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 147 (accept_3_4 4 134 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 147 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 134 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 147
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 147 (accept_3_4 1 134 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  147)))))))))))))) (allB_succ' 15 133 147 (Eq.refl Bool.true) (allA_succ_of_gcd 14 133 147 7 2 19 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 133 147
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 133 147 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 133 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 147 (accept_3_5 11 133 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 133 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 147 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  133 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 147 (accept_3_5 8 133
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133 147 7 1 19 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 133 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 147 (accept_3_5 5 133 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 147 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 133 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 147 (accept_3_5 2 133 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 147 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 147))))))))))))))) (allB_succ' 16 132 147
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 147 3 5 44 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 132 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 132 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 147
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 132 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 147 3 4 44 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 147 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 132 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 132 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 147 3 3 44 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 147
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 132 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 147 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 147 3 2 44 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 147
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 132 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 132 147 3 1 44 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 132 147 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 132 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 147)))))))))))))))) (allB_succ' 17 131 147
  (Eq.refl Bool.true) (allA_succ_of_accept 16 131 147 (accept_3_4 16 131 147 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 131 147 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 131 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 147 (accept_3_4 13 131 147
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 147
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 131 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 131 147 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 131 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 147 (accept_3_4 10 131 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 131 147 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 131 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  131 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 147 (accept_3_4 7 131
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 147
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 131 147 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 131 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 147 (accept_3_4 4 131 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 131 147 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 131 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 2
  131 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 147 (accept_3_4 1 131
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131 147))))))))))))))))) (allB_succ' 18 130 147 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 147 (accept_3_5 17 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 130 147 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 130 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 147 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 130 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 147 (accept_3_5 14 130 147
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  130 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 147
  (Polychromatic418967fa.accept_19_12_16_14_1_3661 12 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 130 147 (accept_3_5 11 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 130 147 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 130 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 147 (accept_3_5 8 130 147
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  130 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 147
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 147 (accept_3_5 5 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 147 (Polychromatic418967fa.accept_22_4_20_15_1_7892 4 130 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 147 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 130 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 147 (accept_3_5 2 130 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 147)))))))))))))))))) (allB_succ' 19 129 147
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 129 147 3 6 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 129 147 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 129 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 147
  (Polychromatic418967fa.accept_13_3_12_4_1_110 16 129 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 147 3 5 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 147 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 129
  147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 147 3 4 43 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 147
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 129 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 147 3 3 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 147 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 129 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 147
  (Polychromatic418967fa.accept_11_7_8_4_1_718 7 129 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 147 3 2 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 147 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 129 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 147 (Polychromatic418967fa.accept_14_4_3_7_1_3702 4 129 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 147 3 1 43 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 147 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 129 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 147))))))))))))))))))) (allB_succ' 20 128 147 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 147 (accept_3_4 19 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 147 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 147 (accept_3_4 16 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 147 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 128 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 147
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 147 (accept_3_4 13 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 147 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 147 (accept_3_4 10 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 147 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 128 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 147
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 147 (accept_3_4 7 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 147 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 147 (accept_3_4 4 128 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 147 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 128 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 147
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 147 (accept_3_4 1 128 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  147)))))))))))))))))))) (allB_succ' 21 127 147 (Eq.refl Bool.true) (allA_succ_of_accept 20 127 147 (accept_3_5 20 127
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 147
  (Polychromatic418967fa.accept_13_6_10_4_1_957 19 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 127 147 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 147 (accept_3_5 17 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 127 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 147 (Polychromatic418967fa.accept_9_6_1_3_1_191
  15 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 147 (accept_3_5 14
  127 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 147
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 127 147 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 147 (accept_3_5 11 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 127 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 147 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 147 (accept_3_5 8
  127 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 147
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 127 147 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 147 (accept_3_5 5 127 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 127 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 147 (Polychromatic418967fa.accept_15_3_7_12_1_372
  3 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 147 (accept_3_5 2
  127 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 147
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 127 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 127 147))))))))))))))))))))) (allB_succ' 22 126 147 (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 147 21 1 6
  7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 147
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 147 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 126 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 147 3 6 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 147
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 126 147 3 5 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 126 147 7 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 147 3 4 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 147 (Polychromatic418967fa.accept_10_1_6_7_1_710
  11 126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 147
  (Polychromatic418967fa.accept_11_10_5_4_1_711 10 126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 147 3 3 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 147 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 126 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 126 147 7 1 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 147 3 2 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 147
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 126 147 3 1 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 126 147 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 147)))))))))))))))))))))) (allB_succ' 23
  125 147 (Eq.refl Bool.true) (allA_succ_of_accept 22 125 147 (accept_3_4 22 125 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 147 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 147
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 147 (accept_3_4 19 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 147 (Polychromatic418967fa.accept_15_2_5_12_1_369 17 125 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 147 (accept_3_4 16 125 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 147 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 125 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 147 (accept_3_4 13 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 147 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 147 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 125 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 147 (accept_3_4 10 125 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 147 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 125 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 147
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 147 (accept_3_4 7 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 147 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 125 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 147 (accept_3_4 4 125 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 147 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 125 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 147 (accept_3_4 1 125 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  147))))))))))))))))))))))) (allB_succ' 24 124 147 (Eq.refl Bool.true) (allA_succ_of_accept 23 124 147 (accept_3_5 23
  124 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 147
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 124 147 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 147 (accept_3_5 20 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 124 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 147 (Polychromatic418967fa.accept_11_7_3_4_1_729
  18 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 147 (accept_3_5 17
  124 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 147
  (Polychromatic418967fa.accept_13_3_7_4_1_435 16 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 124 147 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 147 (accept_3_5 14 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 124 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 147 (Polychromatic418967fa.accept_10_2_4_7_1_352
  12 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 147 (accept_3_5 11
  124 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 147
  (Polychromatic418967fa.accept_9_1_7_3_1_41 10 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 124 147 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 147 (accept_3_5 8 124 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 124 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 147 (Polychromatic418967fa.accept_9_6_7_3_1_436 6
  124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 147 (accept_3_5 5 124
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 147 (Polychromatic418967fa.accept_9_4_7_3_1_43
  4 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 147
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 147 (accept_3_5 2 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 147)))))))))))))))))))))))) (allB_succ' 25 123 147 (Eq.refl Bool.true) (allA_succ_of_gcd 24
  123 147 3 8 41 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 123 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 123 147 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 147 3 7 41 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 147
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 123 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 147 3 6 41 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 147 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 147
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 147 3 5 41 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 123 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 147 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 123 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 147 3 4 41 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 147
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 123 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 147 3 3 41 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 147 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 147
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 147 3 2 41 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 147 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 123 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 147 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 147 3 1 41 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 147
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 147 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 123 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 147))))))))))))))))))))))))) (allB_succ' 26 122 147 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 122 147 (accept_3_4 25 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 147 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 147 (accept_3_4 22 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 147
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 147 (accept_3_4 19 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 147 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 147 (accept_3_4 16 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 147 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 122 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 147
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 147 (accept_3_4 13 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 147 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 147 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 147 (accept_3_4 10 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 147
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 147 (accept_3_4 7 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 147 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 147 (accept_3_4 4 122 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 147 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 122 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 147
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 147 (accept_3_4 1 122 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  147)))))))))))))))))))))))))) (allB_succ' 27 121 147 (Eq.refl Bool.true) (allA_succ_of_accept 26 121 147 (accept_3_5
  26 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 147
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 121 147 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 121 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 147 (accept_3_5 23 121 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 121 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 147 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 147 (accept_3_5 20
  121 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 147
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 121 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 147 (accept_3_5 17 121 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 121 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 147 (Polychromatic418967fa.accept_9_6_4_3_1_203
  15 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 147 (accept_3_5 14
  121 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 147
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 147 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 121 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 147 (accept_3_5 11 121 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 147
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 147 (accept_3_5 8 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 147 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 147 (accept_3_5 5 121 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 147 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 147
  (Polychromatic418967fa.accept_17_3_2_11_1_1895 3 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 147 (accept_3_5 2 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 147 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 121 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 147))))))))))))))))))))))))))) (allB_succ' 28 120 147 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 120 147 3 9 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 147 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 120 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 147 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 120
  147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 147 3 8 40 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 147
  (Polychromatic418967fa.accept_25_23_20_22_1_7891 23 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 120 147 (Polychromatic418967fa.accept_31_22_27_23_1_7890 22 120 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 147 3 7 40 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 147
  (Polychromatic418967fa.accept_13_7_3_4_1_459 20 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 147 (Polychromatic418967fa.accept_18_1_12_3_1_6426 19 120 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 147 3 6 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 147
  (Polychromatic418967fa.accept_22_17_10_15_1_6062 17 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 120 147 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 120 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 147 3 5 40 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 147
  (Polychromatic418967fa.accept_13_1_3_4_1_925 14 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 147 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 120 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 147 3 4 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 147 (Polychromatic418967fa.accept_16_11_8_3_1_3183
  11 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 147
  (Polychromatic418967fa.accept_17_10_1_11_1_2900 10 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 120 147 3 3 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 120 147 (Polychromatic418967fa.accept_17_8_1_11_1_4004 8 120 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 147 (Polychromatic418967fa.accept_13_7_3_4_1_459 7
  120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 147 3 2 40 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 147
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 147 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 120 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 147 3 1 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 147 (Polychromatic418967fa.accept_18_2_12_3_1_2707 2 120 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 147
  (Polychromatic418967fa.accept_13_1_3_4_1_925 1 120 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 147)))))))))))))))))))))))))))) (allB_succ' 29 119 147 (Eq.refl Bool.true) (allA_succ_of_gcd 28 119 147
  7 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 119
  147 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 147 (accept_3_4 25 119 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 147 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 147
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 147 (accept_3_4 22 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  119 147 7 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 119 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 147 (accept_3_4 19 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 147 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 119 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 147 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 119 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 147 (accept_3_4 16 119 147
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 147 (Polychromatic418967fa.accept_9_6_2_3_1_771
  15 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 119 147 7 2 17 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 119 147
  (accept_3_4 13 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 147
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 147 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 119 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 147 (accept_3_4 10 119 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 147 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 147 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 147 7 1 17 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 147
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 147 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 119 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 147 (accept_3_4 4 119 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 147 (Polychromatic418967fa.accept_19_3_5_14_1_3584 3 119 147 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 147
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 147 (accept_3_4 1 119 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  147))))))))))))))))))))))))))))) (allB_succ' 30 118 147 (Eq.refl Bool.true) (allA_succ_of_accept 29 118 147
  (accept_3_5 29 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 147
  (Polychromatic418967fa.accept_19_9_4_14_1_3642 28 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 118 147 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 147 (accept_3_5 26 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 118 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 147 (Polychromatic418967fa.accept_9_6_1_3_1_191
  24 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 147 (accept_3_5 23
  118 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 147
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 118 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 147 (accept_3_5 20 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 118 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 147 (Polychromatic418967fa.accept_11_7_8_4_1_718
  18 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 147 (accept_3_5 17
  118 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 147
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 118 147 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 147 (accept_3_5 14 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 118 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 147 (Polychromatic418967fa.accept_11_1_8_4_1_717
  12 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 147 (accept_3_5 11
  118 147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 147
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 10 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 118 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 147 (accept_3_5 8 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 118 147 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 147 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 147 (accept_3_5 5 118
  147 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 147
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 118 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 118 147 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 147 (accept_3_5 2 118 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 118 147 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 147 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 147)))))))))))))))))))))))))))))) (allB_succ' 31 117 147
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 117 147 3 10 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 147 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 117 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 147
  (Polychromatic418967fa.accept_19_9_3_14_1_2400 28 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 147 3 9 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 147 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 117
  147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 147 3 8 39 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 147
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 147 3 7 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 147 (Polychromatic418967fa.accept_18_2_9_3_1_3825
  20 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 147
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 147 3 6 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 147 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 147 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 117
  147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 147 3 5 39 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 147 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 147 3 4 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 147 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 147
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 147 3 3 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 147 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 147 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 147 3 2 39 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 147
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 147 (Polychromatic418967fa.accept_17_4_15_11_1_6465 4 117 147 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 147 3 1 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 147 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 147
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 147
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 117 147 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 147)))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_147_segment_000))))))))))))))))))))))))))))))


