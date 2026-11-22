-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch154
-- name    : Polychromatic418967fa_Branch154
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:31.733409+00:00
-- url     : https://prove2.me/theorems/cff02e93-faae-46c0-9cb4-23fb090d0155
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

def Polychromatic418967fa.branch_154 : allB 154 154 :=
  allB_succ' 2 153 154 (Eq.refl Bool.true) (allA_succ_of_accept 1 153 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  153 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 154)) (allB_succ' 3 152 154
  (Eq.refl Bool.true) (allA_of_3_1 3 152 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 151 154 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 151 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 154 (accept_3_3 2 151 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 154)))) (allB_succ' 5 150 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 150 154 2 2 75 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 150 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 154 2 1 75 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 154 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 150 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 154))))) (allB_succ' 6 149 154 (Eq.refl
  Bool.true) (allA_of_3_1 6 149 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 148 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 148 154 2 3 74 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 154 (accept_3_3 5 148 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  154 2 2 74 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 148 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 154 2 1 74 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 148 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 148 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 154))))))) (allB_succ' 8 147 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 147 154 7 1 21 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 147 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 154 (accept_3_3 5 147 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 147 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 154 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  147 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 154 (accept_3_3 2 147
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 154 (Polychromatic418967fa.accept_4_1_3_2_1_3
  1 147 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 154)))))))) (allB_succ' 9 146 154
  (Eq.refl Bool.true) (allA_of_3_1 9 146 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 145 154 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 145 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 154 (accept_3_3 8 145 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 145 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 154 (accept_3_3 5 145 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 145 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 154 (accept_3_3 2 145 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 154 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 145 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 154)))))))))) (allB_succ' 11 144 154 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 144 154 2 5 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 144 154 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 144 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 154 2 4 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 154 (Polychromatic418967fa.accept_13_7_1_11_1_732 7
  144 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 154 2 3 72 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 154 (accept_3_3 5
  144 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 154 2 2 72 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 154
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 144 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 154 2 1 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 154 (Polychromatic418967fa.accept_25_1_19_4_1_8396 1 144 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 154))))))))))) (allB_succ' 12 143 154 (Eq.refl Bool.true) (allA_of_3_1
  12 143 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 142 154 (Eq.refl Bool.true) (allA_succ_of_gcd 12
  142 154 2 6 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 142 154 (accept_3_3 11 142 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 154 2 5 71 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 154
  (Polychromatic418967fa.accept_21_9_16_7_1_5222 9 142 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 154 2 4 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 142 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 154 2 3 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 154 (accept_3_3 5 142 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 154 2 2 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 142 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 154 2 1 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 154 (Polychromatic418967fa.accept_13_1_12_11_1_728
  1 142 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 154))))))))))))) (allB_succ' 14
  141 154 (Eq.refl Bool.true) (allA_succ_of_accept 13 141 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 154 (accept_3_3 11 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 154 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 141 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 154 (accept_3_3 8 141 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 154 (accept_3_3 5 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 154 (accept_3_3 2 141 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 154)))))))))))))) (allB_succ' 15 140 154 (Eq.refl
  Bool.true) (allA_of_3_1 15 140 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 139 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 139 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 154 (accept_3_3 14 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 139 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 12
  139 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 154 (accept_3_3 11
  139 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 154
  (Polychromatic418967fa.accept_19_10_6_2_1_6907 10 139 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 139 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 154 (accept_3_3 8 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 139 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 6
  139 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 154 (accept_3_3 5 139
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 154
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 139 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 139 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 154 (accept_3_3 2 139 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 139 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 154)))))))))))))))) (allB_succ' 17 138 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 138 154 2 8 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 138 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 138 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 154 2 7 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  138 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 154 2 6 69 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 154 (accept_3_3 11
  138 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 154 2 5 69 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 138 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 154 2 4 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 154 2 3 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 154 (accept_3_3 5 138 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 154 2 2 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 138 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 154 2 1 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 154 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  138 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 154))))))))))))))))) (allB_succ' 18
  137 154 (Eq.refl Bool.true) (allA_of_3_1 18 137 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 136 154
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 136 154 2 9 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 136 154 (accept_3_3 17 136 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 154 2 8 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 136 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 154 2 7 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 154 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 136 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 154 2 6 68 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 154
  (accept_3_3 11 136 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 154 2 5 68 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 154
  (Polychromatic418967fa.accept_21_9_10_7_1_383 9 136 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 154 2 4 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 136 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 154 2 3 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 154 (accept_3_3 5 136 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 154 2 2 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 3 136 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 154 2 1 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  136 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 154))))))))))))))))))) (allB_succ'
  20 135 154 (Eq.refl Bool.true) (allA_succ_of_accept 19 135 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 154 (accept_3_3 17 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 154 (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 135 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 154 (accept_3_3 14 135 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 154
  (Polychromatic418967fa.accept_17_12_16_1_1_8363 12 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 154 (accept_3_3 11 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 154 (Polychromatic418967fa.accept_20_10_15_14_1_6797 10 135 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 154 (accept_3_3 8 135
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 154 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 154 (accept_3_3 5 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 154 (Polychromatic418967fa.accept_23_4_20_16_1_8395 4 135 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 154 (Polychromatic418967fa.accept_13_3_5_11_1_716 3 135 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 154 (accept_3_3 2 135 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 154)))))))))))))))))))) (allB_succ' 21 134 154
  (Eq.refl Bool.true) (allA_of_3_1 21 134 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 133 154 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 133 154 7 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 133 154 (accept_3_3 20 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 133 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 154 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 133
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 154 (accept_3_3 17 133
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 154
  (Polychromatic418967fa.accept_12_4_1_10_1_221 16 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 133 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 133 154 7 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 133 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 154 (accept_3_3 11 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 154 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 154 (accept_3_3 8 133 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133 154 7 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 133 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 154 (accept_3_3 5 133 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 154 (accept_3_3 2 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 133 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 154)))))))))))))))))))))) (allB_succ' 23 132 154 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  132 154 22 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 132 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 132 154 2 10 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 132 154 (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 132 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 154 2 9 66 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 154 (accept_3_3 17 132 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 154 2 8 66 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 154
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 132 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 154 2 7 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 154 2 6 66 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 154 11 1 12 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 154 2 5 66 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 154
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 132 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 154 2 4 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 154 2 3 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 154 (accept_3_3 5 132 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 154 2 2 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 154 2 1 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 154 (Polychromatic418967fa.accept_15_1_12_4_1_2022
  1 132 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 154)))))))))))))))))))))))
  (allB_succ' 24 131 154 (Eq.refl Bool.true) (allA_of_3_1 24 131 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 130 154 (Eq.refl Bool.true) (allA_succ_of_gcd 24 130 154 2 12 65 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 154 (accept_3_3 23 130 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 154 2 11 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  130 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 154 2 10 65 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 154
  (Polychromatic418967fa.accept_21_19_4_7_1_3775 19 130 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 154 2 9 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 154 (accept_3_3 17 130 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 154 2 8 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 130 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 154 2 7 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 154 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 130 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 154 2 6 65 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 154 (accept_3_3 11
  130 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 154 2 5 65 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 154
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 130 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 154 2 4 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 154 2 3 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 154 (accept_3_3 5 130 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 154 2 2 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 130 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 154 2 1 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 154 (Polychromatic418967fa.accept_20_1_10_14_1_1472
  1 130 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 154)))))))))))))))))))))))))
  (allB_succ' 26 129 154 (Eq.refl Bool.true) (allA_succ_of_accept 25 129 154 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 154 (accept_3_3 23 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 154 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 154 (accept_3_3 20 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 154 (accept_3_3 17 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 154 (accept_3_3 14 129 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 154
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 154 (accept_3_3 11 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 154 (Polychromatic418967fa.accept_16_9_1_10_1_3610 9 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 154 (accept_3_3 8 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 154 (accept_3_3 5 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 129 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 154 (accept_3_3 2 129 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 154)))))))))))))))))))))))))) (allB_succ' 27 128 154
  (Eq.refl Bool.true) (allA_of_3_1 27 128 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 127 154 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 127 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 154 (accept_3_3 26 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 154
  (Polychromatic418967fa.accept_17_7_8_1_1_1373 24 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 154 (accept_3_3 23 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 154 (accept_3_3 20 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 154 (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 127 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 154
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 154 (accept_3_3 17 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 154 (accept_3_3 14 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 154
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 154 (accept_3_3 11 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 154 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 154 (accept_3_3 8 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 154 (Polychromatic418967fa.accept_17_7_8_1_1_1373 7 127 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 154
  (Polychromatic418967fa.accept_19_6_13_2_1_8365 6 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 154 (accept_3_3 5 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 127 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 154 (accept_3_3 2 127 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 154)))))))))))))))))))))))))))) (allB_succ' 29 126
  154 (Eq.refl Bool.true) (allA_succ_of_gcd 28 126 154 14 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 154 2 13 63 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 154
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 126 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 154 2 12 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 154 (accept_3_3 23 126 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 154 2 11 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 126 154 7 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 126 154 2 10 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 126 154 (Polychromatic418967fa.accept_20_19_6_14_1_3906 19 126 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 154 2 9 63 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 154 (accept_3_3 17
  126 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 154 2 8 63 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 154
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 154 14 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 154 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 126 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 154 2 6 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 154 (accept_3_3 11 126 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 154 2 5 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 154 2 4 63 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 154 7 1 18 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 154 2 3 63 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 154 (accept_3_3 5 126 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 154 2 2 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  126 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 154 2 1 63 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 154
  (Polychromatic418967fa.accept_13_1_9_11_1_703 1 126 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 154))))))))))))))))))))))))))))) (allB_succ' 30 125 154 (Eq.refl Bool.true) (allA_of_3_1 30 125 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 124 154 (Eq.refl Bool.true) (allA_succ_of_gcd 30 124 154 2 15
  62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 154
  (accept_3_3 29 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 154 2 14 62 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 154
  (Polychromatic418967fa.accept_13_1_7_11_1_702 27 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 154 2 13 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 124 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 154 2 12 62 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 154 (accept_3_3 23 124 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 154 2 11 62 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 154 2 10 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 124 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 124 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 154 2 9 62 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 154 (accept_3_3 17 124 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 154 2 8 62 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 124 154 2 7 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 124 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 154 2 6 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 154 (accept_3_3 11 124 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 154 2 5 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 154 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 124 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 154 2 4 62 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 154 2 3 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 154 (accept_3_3 5 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  154 2 2 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 124 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 154 2 1 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 124 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 124 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 154))))))))))))))))))))))))))))))) (allB_succ' 32 123 154
  (Eq.refl Bool.true) (allA_succ_of_accept 31 123 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 154 (accept_3_3 29 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 154 (Polychromatic418967fa.accept_16_12_11_10_1_1667 28 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 154 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 154 (accept_3_3 26 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 154
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 154 (accept_3_3 23 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 123 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 154 (accept_3_3 20 123 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 154 (accept_3_3 17 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 154 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 154 (accept_3_3 14 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 154 (accept_3_3 11 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 154 (Polychromatic418967fa.accept_21_10_18_7_1_5212 10 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 154 (accept_3_3 8 123 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 154 (accept_3_3 5 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 123 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 154 (accept_3_3 2 123 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 154)))))))))))))))))))))))))))))))) (allB_succ' 33
  122 154 (Eq.refl Bool.true) (allA_of_3_1 33 122 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 121 154
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 121 154 11 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 121 154 (accept_3_3 32 121 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 121 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 30
  121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 154 (accept_3_3 29
  121 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 154
  (Polychromatic418967fa.accept_12_4_1_10_1_221 28 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 154 (accept_3_3 26 121 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 154 (Polychromatic418967fa.accept_9_6_4_1_1_390
  24 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 154 (accept_3_3 23
  121 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 121 154 11 2 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 121 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 154 (accept_3_3 20 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 121 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 154 (accept_3_3 17 121 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 154 (accept_3_3 14 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 154 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 121 154 11 1 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 121 154
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 154 (accept_3_3 8 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 154 (accept_3_3 5 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 121 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 154 (accept_3_3 2 121 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 154 (Polychromatic418967fa.accept_16_1_9_10_1_4740 1 121 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 154)))))))))))))))))))))))))))))))))) (allB_succ' 35
  120 154 (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 154 2 17 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 120 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 154 2 16 60 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 154 2 15 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 154 (accept_3_3 29 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 154 2 14 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 120 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 154 2 13 60 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 154 2 12 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 154 (accept_3_3 23 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 154 2 11 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 154 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 120 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 154 2 10 60 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 154
  (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 120 154 2 9 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 120 154 (accept_3_3 17 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 154 2 8 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 120 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 154 2 7 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 154 2 6 60 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 154 (accept_3_3 11
  120 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 154 2 5 60 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 154
  (Polychromatic418967fa.accept_18_9_12_10_1_387 9 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 154 2 4 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 154 2 3 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 154 (accept_3_3 5 120 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 154 2 2 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 154 (Polychromatic418967fa.accept_19_3_6_2_1_6910 3 120 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 154 2 1 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289
  1 120 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  154))))))))))))))))))))))))))))))))))) (allB_succ' 36 119 154 (Eq.refl Bool.true) (allA_of_3_1 36 119 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 118 154 (Eq.refl Bool.true) (allA_succ_of_gcd 36 118 154 2 18 59 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 118 154
  (accept_3_3 35 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 118 154 2 17 59 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 118 154
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 118 154 2 16 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 118 154 (Polychromatic418967fa.accept_19_12_4_2_1_4121 31 118 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 118 154 2 15 59 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 118 154 (accept_3_3 29 118 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 118 154 2 14 59 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 118 154
  (Polychromatic418967fa.accept_21_6_13_7_1_8394 27 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 118 154 2 13 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 118 154 (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 118 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 118 154 2 12 59 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 118 154 (accept_3_3 23 118 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 118 154 2 11 59 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 118 154
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 118 154 2 10 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 118 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 118 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 118 154 2 9 59 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 118 154 (accept_3_3 17 118 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 118 154 2 8 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 118 154
  (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 154 2 7 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 154 (Polychromatic418967fa.accept_23_13_3_16_1_8355 13 118 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 154 2 6 59 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 154 (accept_3_3 11
  118 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 154 2 5 59 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 154 2 4 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 154 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 118 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 154 2 3 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 154 (accept_3_3 5 118 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 154 2 2 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 154 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 118 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 154 2 1 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 154 (Polychromatic418967fa.accept_26_1_14_24_1_8393
  1 118 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  154))))))))))))))))))))))))))))))))))))) (allB_succ' 38 117 154 (Eq.refl Bool.true) (allA_succ_of_accept 37 117 154
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 117 154 (Polychromatic418967fa.accept_19_17_3_2_1_1725 36 117 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 154 (accept_3_3 35 117 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 117 154 (Polychromatic418967fa.accept_25_9_17_4_1_8392 34 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 154
  (Polychromatic418967fa.accept_10_3_7_4_1_584 33 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 154 (accept_3_3 32 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 154 (accept_3_3 29 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 154 (Polychromatic418967fa.accept_16_12_5_10_1_3561 28 117
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 154 (accept_3_3 26 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 154 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 154 (accept_3_3 23 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 117
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 154
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 154 (accept_3_3 20 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 154 (accept_3_3 17 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 154 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 117
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 154 (accept_3_3 14 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 154 (accept_3_3 11 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 154 (Polychromatic418967fa.accept_25_10_17_4_1_8391 10 117
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 154
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 154 (accept_3_3 8 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 117 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 154 (accept_3_3 5 117 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 154 (Polychromatic418967fa.accept_21_4_12_7_1_5174 4 117 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 154 (accept_3_3 2 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 154)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 116 154 (Eq.refl Bool.true)
  (allA_of_3_1 39 116 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 115 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 115 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 154 (accept_3_3 38 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 154 (Polychromatic418967fa.accept_10_6_5_4_1_571
  36 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 154 (accept_3_3 35
  115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 154
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 34 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 154 (accept_3_3 32 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 154 (Polychromatic418967fa.accept_9_3_7_1_1_143
  30 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 154 (accept_3_3 29
  115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 154
  (Polychromatic418967fa.accept_12_4_7_10_1_563 28 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 154 (accept_3_3 26 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 154 (Polychromatic418967fa.accept_9_6_7_1_1_145
  24 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 154 (accept_3_3 23
  115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 154
  (Polychromatic418967fa.accept_9_4_7_1_1_379 22 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 154 (accept_3_3 20 115 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 115 154 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 115 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 154
  (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 154 (accept_3_3 17 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 154 (accept_3_3 14 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 154 (accept_3_3 11 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 154 (Polychromatic418967fa.accept_20_10_15_14_1_6797 10 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 154 (accept_3_3 8 115 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 154 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 115 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 154 (accept_3_3 5 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 154 (accept_3_3 2 115 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 154))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 114 154 (Eq.refl Bool.true) (allA_succ_of_gcd 40 114 154 2 20 57 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 154 2 19 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 154 (Polychromatic418967fa.accept_21_16_9_7_1_6709 37 114 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 154 2 18 57 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 154 (accept_3_3 35 114 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 154 2 17 57 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 154 2 16 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 114 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 154 2 15 57 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 154 (accept_3_3 29 114 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 154 2 14 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 154 (Polychromatic418967fa.accept_12_3_6_10_1_576
  27 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 154 2 13 57 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 154 2 12 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 154 (accept_3_3 23 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 154 2 11 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 154 2 10 57 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 154
  (Polychromatic418967fa.accept_21_19_9_7_1_8366 19 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 154 2 9 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 154 (accept_3_3 17 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 154 2 8 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 154 2 7 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 114 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 154 2 6 57 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 154 (accept_3_3 11 114 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 154 2 5 57 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 154 2 4 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 154 2 3 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 154 (accept_3_3 5 114 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 154 2 2 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 154 2 1 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 154 (Polychromatic418967fa.accept_13_1_10_11_1_1280
  1 114 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  154))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 113 154 (Eq.refl Bool.true) (allA_of_3_1 42 113 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 112 154 (Eq.refl Bool.true) (allA_succ_of_gcd 42 112 154 14 3
  8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 154
  (accept_3_3 41 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 154 2 20 56 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 154 2 19 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 112 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 154 2 18 56 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 112 154 7 5 16 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 112 154 2 17 56 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 154 2 16 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 112 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 112 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 154 2 15 56 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 154 (accept_3_3 29 112 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 154 14 2 8 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 154
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 112 154 2 13 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 112 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 154 2 12 56 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 154 (accept_3_3 23 112 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 154 2 11 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 112 154 7 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 112 154 2 10 56 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 154 2 9 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 154 (accept_3_3 17 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 154 2 8 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 154 14 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 154 2 6 56 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 154 (accept_3_3 11 112 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 154 2 5 56 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 154
  (Polychromatic418967fa.accept_13_9_8_11_1_725 9 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 154 2 4 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 112 154 7 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 112 154 2 3 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 154 (accept_3_3 5 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  154 2 2 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 112 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 154 2 1 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 112 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 154))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  111 154 (Eq.refl Bool.true) (allA_succ_of_accept 43 111 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 154 (accept_3_3 41 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 154 (accept_3_3 38 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 154
  (Polychromatic418967fa.accept_19_17_16_2_1_8390 36 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 154 (accept_3_3 35 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 111 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 154 (accept_3_3 32 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 154 (accept_3_3 29 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 154 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 154 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 154 (accept_3_3 26 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 154 (accept_3_3 23 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 154 (accept_3_3 20 111 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 154 (accept_3_3 17 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 154 (accept_3_3 14 111 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 154
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 154 (accept_3_3 11 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 154 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 111 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 154 (accept_3_3 8 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 154 (accept_3_3 5 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 111 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 154 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 154 (accept_3_3 2 111 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  154)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 110 154 (Eq.refl Bool.true) (allA_of_3_1 45 110 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 109 154 (Eq.refl Bool.true) (allA_succ_of_accept 45 109 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 154 (accept_3_3 44 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 154 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 154 (accept_3_3 41 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 154 (accept_3_3 38 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 154 (Polychromatic418967fa.accept_16_5_13_10_1_3664 37 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 154 (Polychromatic418967fa.accept_19_17_14_2_1_4116 36 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 154 (accept_3_3 35 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 154 (Polychromatic418967fa.accept_18_16_1_10_1_2029 34 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 154 (accept_3_3 32 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 154 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 154 (accept_3_3 29 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 154 (accept_3_3 26 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 154 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 154 (Polychromatic418967fa.accept_19_5_14_2_1_1716 24 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 154 (accept_3_3 23 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 154 (Polychromatic418967fa.accept_21_1_4_7_1_3689 22 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 154 (accept_3_3 20 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 154 (accept_3_3 17 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 154 (accept_3_3 14 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 154 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 154 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 154 (accept_3_3 11 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 154 (Polychromatic418967fa.accept_17_10_7_1_1_7024 10 109
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 154 (accept_3_3 8 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 154 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 154 (accept_3_3 5 109 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 109 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 154 (accept_3_3 2 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 154 (Polychromatic418967fa.accept_19_1_14_2_1_4134 1 109 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 154)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 108 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 108 154 2 23 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 154 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 108 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 154 2 22 54 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 154
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 43 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 154 2 21 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 154 (accept_3_3 41 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 154 2 20 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 154 2 19 54 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 154
  (Polychromatic418967fa.accept_15_7_3_4_1_574 37 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 154 2 18 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 154 (accept_3_3 35 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 154 2 17 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 154 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 108 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 154 2 16 54 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 154
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 154 2 15 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 154 (accept_3_3 29 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 154 2 14 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 154 (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 108 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 154 2 13 54 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 154
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 108 154 2 12 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 154 (accept_3_3 23 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 154 2 11 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 154 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 108 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 154 2 10 54 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 154 2 9 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 154 (accept_3_3 17 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  108 154 2 8 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 108 154 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 154 2 7 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 154 (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 108 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 154 2 6 54 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 154 (accept_3_3 11
  108 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 154 2 5 54 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 154 2 4 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 154 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 108 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 154 2 3 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 154 (accept_3_3 5 108 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 154 2 2 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 154 (Polychromatic418967fa.accept_16_3_12_10_1_315 3 108 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 154 2 1 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 154 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1
  108 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  154))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 107 154 (Eq.refl Bool.true) (allA_of_3_1 48 107 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 106 154 (Eq.refl Bool.true) (allA_succ_of_gcd 48 106 154 2 24
  53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 106 154
  (accept_3_3 47 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 106 154 2 23 53 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 106 154
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 106 154 2 22 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 106 154 (Polychromatic418967fa.accept_13_4_2_11_1_733 43 106 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 106 154 2 21 53 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 106 154 (accept_3_3 41 106 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 106 154 2 20 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 106 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 106 154 2 19 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 106 154 (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 106 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 106 154 2 18 53 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 106 154 (accept_3_3 35 106 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 106 154 2 17 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 106 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 106 154 2 16 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 106 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 106 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 106 154 2 15 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 106 154 (accept_3_3 29 106 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 106 154 2 14 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 106 154 (Polychromatic418967fa.accept_15_12_1_4_1_2899
  27 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 154 2 13 53 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 154
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 154 2 12 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 154 (accept_3_3 23 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 154 2 11 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 106 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 154 2 10 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 154
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 19 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 106 154 2 9 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 106 154 (accept_3_3 17 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 154 2 8 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 106 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 106 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 154 2 7 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 154 2 6 53 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 154 (accept_3_3 11
  106 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 154 2 5 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 154
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 154 2 4 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 154 (Polychromatic418967fa.accept_23_7_14_16_1_8389 7 106 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 154 2 3 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 154 (accept_3_3 5 106 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 154 2 2 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 106 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 154 2 1 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 154 (Polychromatic418967fa.accept_18_1_16_10_1_2065
  1 106 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  154))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 105 154 (Eq.refl Bool.true) (allA_succ_of_gcd 49
  105 154 7 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 105 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 154 (accept_3_3 47 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 154 (Polychromatic418967fa.accept_18_9_15_10_1_395 45 105
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 154 (accept_3_3 44 105
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 154 7 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 105 154 (accept_3_3 41 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 154 (accept_3_3 38 105 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 105 154 7 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 105 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 154 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 105
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 154 (accept_3_3 32 105
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 105 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 154 (accept_3_3 29 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 105 154 7 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 105 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 154 (accept_3_3 26 105 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 154
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 154 (accept_3_3 23 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 154 7 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 154 (accept_3_3 20 105 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 154 (accept_3_3 17 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 105 154 7 2 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 154
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 154 (accept_3_3 11 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 154 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 105 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 154
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 154 (accept_3_3 8 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105
  154 7 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  105 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 154 (accept_3_3 5 105 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 105 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 154 (accept_3_3 2 105 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  105 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  154)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 104 154 (Eq.refl Bool.true) (allA_of_3_1 51 104
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 103 154 (Eq.refl Bool.true) (allA_succ_of_accept 51 103
  154 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 154 (accept_3_3 50 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 154 (accept_3_3 47 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 154 (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 103 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 154 (accept_3_3 44 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 154 (accept_3_3 41 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 154 (accept_3_3 38 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 154 (accept_3_3 35 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 103 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 154 (accept_3_3 32 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 154 (Polychromatic418967fa.accept_20_11_3_14_1_5336 31 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 154 (accept_3_3 29 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 154 (accept_3_3 26 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 154 (accept_3_3 23 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 154 (Polychromatic418967fa.accept_18_4_13_10_1_2064 22 103 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 154 (accept_3_3 20 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 154 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 154 (Polychromatic418967fa.accept_21_18_19_7_1_5165 18 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 154 (accept_3_3 17 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 154 (accept_3_3 14 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 154 (accept_3_3 11 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 103 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 154 (accept_3_3 8 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 154 (accept_3_3 5 103 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 154 (accept_3_3 2 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 154)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 102 154 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 102 154 2 26 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 102 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 102 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 154 2 25 51 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 154 2 24 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 154 (accept_3_3 47 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 154 2 23 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 102 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 154 2 22 51 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 154 2 21 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 154 (accept_3_3 41 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 154 2 20 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 154 2 19 51 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 154
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 154 2 18 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 154 (accept_3_3 35 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 154 2 17 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 102 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 154 2 16 51 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 154 2 15 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 154 (accept_3_3 29 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 154 2 14 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 102 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 154 2 13 51 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 154 2 12 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 154 (accept_3_3 23 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 154 2 11 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 102 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 154 2 10 51 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 154
  (Polychromatic418967fa.accept_21_19_18_7_1_8388 19 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 102 154 2 9 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 102 154 (accept_3_3 17 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 154 2 8 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 102 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 154 2 7 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 154 2 6 51 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 154 (accept_3_3 11
  102 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 154 2 5 51 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 154 2 4 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 154 2 3 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 154 (accept_3_3 5 102 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 154 2 2 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 154 2 1 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 154 (Polychromatic418967fa.accept_15_1_12_4_1_2022
  1 102 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  154))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 101 154 (Eq.refl Bool.true) (allA_of_3_1 54
  101 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 100 154 (Eq.refl Bool.true) (allA_succ_of_gcd 54 100
  154 2 27 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  100 154 (accept_3_3 53 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 100 154 2 26 50 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 100 154
  (Polychromatic418967fa.accept_15_6_10_4_1_150 51 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 100 154 2 25 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 100 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 100 154 2 24 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 100 154 (accept_3_3 47 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 100 154 2 23 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 100 154
  (Polychromatic418967fa.accept_19_7_5_2_1_2842 45 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 100 154 2 22 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 100 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 154 2 21 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 154 (accept_3_3 41 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 154 2 20 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 154
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 154 2 19 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 154 2 18 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 100 154 (accept_3_3 35 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 100 154 2 17 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 154
  (Polychromatic418967fa.accept_13_7_9_11_1_705 33 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 154 2 16 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 100 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 154 2 15 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 154 (accept_3_3 29 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 154 2 14 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 154
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 100 154 2 13 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 100 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 154 2 12 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 154 (accept_3_3 23 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 154 2 11 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 154
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 154 2 10 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 100 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 154 2 9 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 154 (accept_3_3 17 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 154 2 8 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 154
  (Polychromatic418967fa.accept_13_2_9_11_1_258 15 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 154 2 7 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 100 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 154 2 6 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 154 (accept_3_3 11 100 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 154 2 5 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 154 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 100 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 154 2 4 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 154 2 3 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 154 (accept_3_3 5 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  154 2 2 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 154 (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 100 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 154 2 1 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 100 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 99 154 (Eq.refl Bool.true) (allA_succ_of_gcd 55 99 154 11 5 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 99 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 99 154 (accept_3_3 53 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  99 154 (Polychromatic418967fa.accept_19_14_4_2_1_2840 52 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 99 154 (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 154 (accept_3_3 50 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 48 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 154 (accept_3_3 47 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 154 (Polychromatic418967fa.accept_20_6_19_14_1_8387 46 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 99 154 11 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 154 (accept_3_3 41 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 154 (Polychromatic418967fa.accept_13_1_8_11_1_724 40 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 154 (Polychromatic418967fa.accept_16_7_3_10_1_3614 39 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 154 (accept_3_3 38 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 154
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 154 (accept_3_3 35 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 154 (Polychromatic418967fa.accept_21_13_15_7_1_5209 34 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 99 154 11 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 99 154 (accept_3_3 32 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 154 (accept_3_3 29 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 154 (Polychromatic418967fa.accept_10_8_9_4_1_961
  28 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 154
  (Polychromatic418967fa.accept_13_1_8_11_1_724 27 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 154 (accept_3_3 26 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 154 (Polychromatic418967fa.accept_19_5_4_2_1_6840 24 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 154 (accept_3_3 23 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 154 11 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 154 (accept_3_3 20 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 154 (accept_3_3 17 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 154 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 154 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 154 (accept_3_3 14 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 154
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 99 154 11 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 99 154 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 99 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 154 (accept_3_3 8 99 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 154 (accept_3_3 5 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  154 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 99 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 154 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 154 (accept_3_3 2 99 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 98 154 (Eq.refl Bool.true) (allA_of_3_1 57
  98 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 97 154 (Eq.refl Bool.true) (allA_succ_of_accept 57 97
  154 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 154 (accept_3_3 56 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 154 (Polychromatic418967fa.accept_26_2_19_24_1_6388 54 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 154 (accept_3_3 53 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 97 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 154 (accept_3_3 50 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 154 (accept_3_3 47 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 154 (Polychromatic418967fa.accept_21_4_13_7_1_8386 46 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 154 (accept_3_3 44 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 154 (accept_3_3 41 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 154 (accept_3_3 38 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 154 (Polychromatic418967fa.accept_21_16_13_7_1_8385 37 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 154 (Polychromatic418967fa.accept_21_15_13_7_1_5175 36 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 154 (accept_3_3 35 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 154 (Polychromatic418967fa.accept_13_8_6_11_1_1979 34 97
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 154 (accept_3_3 32 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 154 (accept_3_3 29 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 154 (accept_3_3 26 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 154 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 154 (accept_3_3 23 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 154 (accept_3_3 20 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 154 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 154 (accept_3_3 17 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 154 (accept_3_3 14 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 154 (accept_3_3 11 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 154 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 97 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 154 (accept_3_3 8 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 154 (accept_3_3 5 97 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 97 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 154 (accept_3_3 2 97 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 154 (Polychromatic418967fa.accept_10_1_7_4_1_968 1
  97 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 96 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 96 154 2 29 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 96 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 96 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 154 2 28 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 55
  96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 154 2 27 48 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 154 (accept_3_3 53
  96 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 154 2 26 48 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 154
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 51 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 154 2 25 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 154 2 24 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 154 (accept_3_3 47 96 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 154 2 23 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 96 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 154 2 22 48 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 154 2 21 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 154 (accept_3_3 41 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96
  154 2 20 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  96 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 96 154 2 19 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 96 154 (Polychromatic418967fa.accept_19_18_1_2_1_5430 37 96 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 154 2 18 48 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 154 (accept_3_3 35 96 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 154 2 17 48 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 154
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 154 2 16 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 154 2 15 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 154 (accept_3_3 29 96 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 154 2 14 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 154 (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 96
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 154 2 13 48 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 154 2 12 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 154 (accept_3_3 23 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  154 2 11 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 154 2 10 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 96 154 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 96 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 154 2 9 48 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 154 (accept_3_3 17 96 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 154 2 8 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 96 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 154 2 7 48 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 154
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 154 2 6 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 154 (accept_3_3 11 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  154 2 5 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 154 2 4 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 154 2 3 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 154 (accept_3_3 5 96 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 154 2 2 48 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 154 2 1 48 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 154
  (Polychromatic418967fa.accept_21_1_12_7_1_3783 1 96 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 95 154 (Eq.refl Bool.true)
  (allA_of_3_1 60 95 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 94 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 94 154 2 30 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 94 154 (accept_3_3 59 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94
  154 2 29 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  94 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 94 154 2 28 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 94 154 (Polychromatic418967fa.accept_16_7_14_10_1_3544 55 94 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 154 2 27 47 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 154 (accept_3_3 53 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 154 2 26 47 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 94 154 2 25 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 94 154 (Polychromatic418967fa.accept_13_10_3_11_1_1923 49 94 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 154 2 24 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 154 (accept_3_3 47 94 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 154 2 23 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 154 (Polychromatic418967fa.accept_16_13_14_10_1_1669 45 94
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 154 2 22 47 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 154 2 21 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 94 154 (accept_3_3 41 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94
  154 2 20 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  94 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 94 154 2 19 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 94 154 (Polychromatic418967fa.accept_16_5_14_10_1_3644 37 94 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 154 2 18 47 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 154 (accept_3_3 35 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 154 2 17 47 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 94 154 2 16 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 94 154 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 94 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 154 2 15 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 154 (accept_3_3 29 94 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 154 2 14 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 154 2 13 47 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 154 2 12 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 94 154 (accept_3_3 23 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94
  154 2 11 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  94 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 94 154 2 10 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 94 154 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 94 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 154 2 9 47 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 154 (accept_3_3 17 94 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 154 2 8 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 94 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 154 2 7 47 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 154
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 94 154 2 6 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 94 154 (accept_3_3 11 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 94 154 2 5 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 94 154 (Polychromatic418967fa.accept_19_9_18_2_1_8383 9 94 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 154 2 4 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 154 2 3 47 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 154 (accept_3_3 5 94 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 154 2 2 47 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 154 2 1 47 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 154
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 94 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 93 154 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 60
  93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 154 (accept_3_3 59 93
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 93 154 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 154 (accept_3_3 56 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 154 (Polychromatic418967fa.accept_12_6_9_10_1_565
  54 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 154 (accept_3_3 53
  93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 52 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 154 (accept_3_3 50 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 154 (Polychromatic418967fa.accept_13_9_2_11_1_1964
  48 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 154 (accept_3_3 47
  93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 154
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 93 154 (Polychromatic418967fa.accept_17_11_8_1_1_3362 45 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 154 (accept_3_3 44 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 154 (accept_3_3 41 93
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 154 (accept_3_3 38 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 154
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 154 (accept_3_3 35 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 154 (accept_3_3 32 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 154 (accept_3_3 29 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 154 (Polychromatic418967fa.accept_16_12_13_10_1_2637 28 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 154 (accept_3_3 26 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 154 (accept_3_3 23 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 154 (Polychromatic418967fa.accept_16_5_13_10_1_3664 21 93 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 154 (accept_3_3 20 93 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 154 (accept_3_3 17 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 154 (accept_3_3 14 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 154
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 154 (accept_3_3 11 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 154 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 154 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 154 (accept_3_3 8 93 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 154 (accept_3_3 5 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 93 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 154 (accept_3_3 2 93 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 92 154 (Eq.refl Bool.true)
  (allA_of_3_1 63 92 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 91 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 91 154 7 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 91 154 (accept_3_3 62 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 154 (Polychromatic418967fa.accept_16_12_11_10_1_1667 60 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 154 (accept_3_3 59 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 154 (Polychromatic418967fa.accept_19_1_15_2_1_6950 58 91
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 91 154 7 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 91 154 (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 91 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 154 (Polychromatic418967fa.accept_17_3_6_1_1_8382 54 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 154 (accept_3_3 53 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 154 (Polychromatic418967fa.accept_12_4_7_10_1_563
  52 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 154 (accept_3_3 50 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91
  154 7 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  91 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 91 154 (accept_3_3 47 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 91 154 (Polychromatic418967fa.accept_17_12_6_1_1_4517 46 91 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 154 (accept_3_3 44 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 154
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 43 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 91 154 7 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 91 154 (accept_3_3 41 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 154 (accept_3_3 38 91 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 154
  (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 91 154 7 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 91 154 (Polychromatic418967fa.accept_18_16_1_10_1_2029 34 91 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 154 (accept_3_3 32 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 154
  (Polychromatic418967fa.accept_16_15_11_10_1_3639 31 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 154 (Polychromatic418967fa.accept_19_11_15_2_1_4096 30 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 154 (accept_3_3 29 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 154 7 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 91 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 154 (accept_3_3 26 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 154
  (Polychromatic418967fa.accept_23_1_22_16_1_8381 24 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 154 (accept_3_3 23 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 154 (Polychromatic418967fa.accept_17_5_6_1_1_5735 22 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 91 154 7 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 91 154 (accept_3_3 20 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 91 154 (Polychromatic418967fa.accept_17_2_6_1_1_8357 19 91 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 154 (accept_3_3 17 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 154 (Polychromatic418967fa.accept_12_4_7_10_1_563
  16 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 154 7 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 154 (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 91
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 154 (accept_3_3 11 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 154
  (Polychromatic418967fa.accept_20_10_11_14_1_8380 10 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 154 (accept_3_3 8 91 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 154 7 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 91 154 (Polychromatic418967fa.accept_19_6_15_2_1_2857 6 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 154 (accept_3_3 5 91 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 91 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 154 (accept_3_3 2 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 91 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 90 154 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 90 154 2 32 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 90 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 90 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 154 2 31 45 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 154
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 61 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 154 2 30 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 154 (accept_3_3 59 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90
  154 2 29 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  90 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 90 154 2 28 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 90 154 (Polychromatic418967fa.accept_17_4_5_1_1_5776 55 90 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 154 2 27 45 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 154 (accept_3_3 53 90 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 154 2 26 45 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 154
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 154 2 25 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 49 90 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 154 2 24 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 154 (accept_3_3 47 90 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 154 2 23 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 90 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 154 2 22 45 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 154
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 43 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 154 2 21 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 154 (accept_3_3 41 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90
  154 2 20 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  90 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 90 154 2 19 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 90 154 (Polychromatic418967fa.accept_21_16_6_7_1_6764 37 90 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 154 2 18 45 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 154 (accept_3_3 35 90 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 154 2 17 45 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 154 2 16 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 154 (Polychromatic418967fa.accept_19_12_14_2_1_1692 31 90 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 154 2 15 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 154 (accept_3_3 29 90 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 154 2 14 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 154 2 13 45 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 154
  (Polychromatic418967fa.accept_20_5_10_14_1_5317 25 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 154 2 12 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 154 (accept_3_3 23 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90
  154 2 11 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  90 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 90 154 2 10 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 90 154 (Polychromatic418967fa.accept_24_19_18_10_1_8351 19 90 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 154 2 9 45 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 154 (accept_3_3 17 90 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 154 2 8 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 154 2 7 45 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 154
  (Polychromatic418967fa.accept_21_13_6_7_1_1237 13 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 154 2 6 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 154 (accept_3_3 11 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90
  154 2 5 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  90 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 90 154 2 4 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 90 154 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 90 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 154 2 3 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 154 (accept_3_3 5 90 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 154 2 2 45 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 90 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 154 2 1 45 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 154
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 90 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 89 154 (Eq.refl
  Bool.true) (allA_of_3_1 66 89 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 88 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 88 154 22 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 88 154 (accept_3_3 65 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88
  154 2 32 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  88 154 (Polychromatic418967fa.accept_19_6_12_2_1_8379 63 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 154 2 31 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 88 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 154 2 30 44 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 154 (accept_3_3 59 88 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 154 2 29 44 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 154 2 28 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 88 154 11 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 88 154 2 27 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 154 (accept_3_3 53 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  154 2 26 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 154 2 25 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 154 2 24 44 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 154 (accept_3_3 47 88 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 154 2 23 44 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 154
  (Polychromatic418967fa.accept_20_5_8_14_1_5341 45 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 154 22 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 154 2 21 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 154 (accept_3_3 41 88 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 154 2 20 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 88 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 154 2 19 44 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 154 2 18 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 154 (accept_3_3 35 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  154 2 17 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 88
  154 11 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 88
  154 2 16 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31
  88 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 88 154 2 15 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 88 154 (accept_3_3 29 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 154 2 14 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 88 154 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 154 2 13 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 154 (Polychromatic418967fa.accept_12_1_4_10_1_209
  25 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 154 2 12 44 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 154 (accept_3_3 23
  88 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 154 22 1 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 88 154 2 10 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 88 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 154 2 9 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 154 (accept_3_3 17 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 88 154 2 8 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 88 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 88 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 154 2 7 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 154 2 6 44 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 88 154 11 1 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 88 154 2 5 44 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 154 2 4 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 154 2 3 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 154 (accept_3_3 5 88 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 154 2 2 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 88 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 154 2 1 44 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  88 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 87 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 87 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 154 (accept_3_3 65 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 154 (Polychromatic418967fa.accept_17_13_2_1_1_4483
  64 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 154
  (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 154 (accept_3_3 62 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 154 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 154 (accept_3_3 59 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 154 (accept_3_3 56 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 154 (accept_3_3 53 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 154
  (Polychromatic418967fa.accept_10_1_7_4_1_968 51 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 154 (accept_3_3 50 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 154 (accept_3_3 47 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 154 (Polychromatic418967fa.accept_13_7_9_11_1_705 46 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 154 (accept_3_3 44 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 154 (accept_3_3 41 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 154 (accept_3_3 38 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 154 (Polychromatic418967fa.accept_21_15_3_7_1_6748 36 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 154 (accept_3_3 35 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 154 (accept_3_3 32 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 154 (accept_3_3 29 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 154 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 154
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 154 (accept_3_3 26 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 154 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 154 (accept_3_3 23 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 154 (accept_3_3 20 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 154 (accept_3_3 17 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 154
  (Polychromatic418967fa.accept_13_2_9_11_1_258 15 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 154 (accept_3_3 14 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 154 (accept_3_3 11 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 154 (Polychromatic418967fa.accept_19_10_11_2_1_8354 10 87 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 154 (accept_3_3 8 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 154 (accept_3_3 5 87 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 87 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 154 (accept_3_3 2 87 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 86 154 (Eq.refl Bool.true)
  (allA_of_3_1 69 86 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 85 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 154 (accept_3_3 68 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 154 (accept_3_3 65 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 154
  (Polychromatic418967fa.accept_12_4_1_10_1_221 64 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 154 (accept_3_3 62 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 60
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 154 (accept_3_3 59 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 154
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 154 (accept_3_3 56 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 154 (Polychromatic418967fa.accept_15_9_10_4_1_2055
  54 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 154 (accept_3_3 53
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 52 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 154 (accept_3_3 50 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 85 154 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 48
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 154 (accept_3_3 47 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 46 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 154 (accept_3_3 44 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 154 (accept_3_3 41 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 154
  (Polychromatic418967fa.accept_12_4_1_10_1_221 40 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 154 (accept_3_3 38 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 85 154 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 154 (Polychromatic418967fa.accept_10_6_5_4_1_571
  36 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 154 (accept_3_3 35
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 34 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 154 (accept_3_3 32 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 30
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 154 (accept_3_3 29 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 154
  (Polychromatic418967fa.accept_12_4_1_10_1_221 28 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 154 (accept_3_3 26 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 85 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 24
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 154 (accept_3_3 23 85
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 154
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 22 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 154 (accept_3_3 20 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 154 (Polychromatic418967fa.accept_13_5_7_11_1_3470
  18 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 154 (accept_3_3 17
  85 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 154 (accept_3_3 14 85 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 85 154 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 85 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 154 (accept_3_3 11 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 154 (Polychromatic418967fa.accept_20_10_5_14_1_8378 10 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 154 (accept_3_3 8 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 154 (accept_3_3 5 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 85 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 154 (accept_3_3 2 85 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 154 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 85 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 84 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 84 154 14 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 84 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 154 2 34 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 67
  84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 154 2 33 42 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 154 (accept_3_3 65
  84 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 154 2 32 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 154 7 9 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 154 2 31 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 154 2 30 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 84 154 (accept_3_3 59 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84
  154 2 29 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  84 154 (Polychromatic418967fa.accept_13_5_6_11_1_1933 57 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 84 154 14 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 84 154 (Polychromatic418967fa.accept_15_10_9_4_1_2924 55 84 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 154 2 27 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 154 (accept_3_3 53 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 154 2 26 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 154 2 25 42 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 84 154 7 7 12 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 154 2 24 42 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 154 (accept_3_3 47
  84 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 154 2 23 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 154
  (Polychromatic418967fa.accept_18_9_12_10_1_387 45 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 154 2 22 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 154 14 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 154 (accept_3_3 41 84 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 84 154 2 20 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 84 154 (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 154 2 19 42 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 154
  (Polychromatic418967fa.accept_23_14_15_16_1_8377 37 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 84 154 2 18 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 154 7 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 154 2 17 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 154 2 16 42 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 154 2 15 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 154 (accept_3_3 29 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  154 14 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 154 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 84 154 2 13 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 84 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 154 2 12 42 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 154 (accept_3_3 23 84 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 154 2 11 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 154 7 3 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 154 2 10 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 154
  (Polychromatic418967fa.accept_17_2_16_1_1_2260 19 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 154 2 9 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 154 (accept_3_3 17 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  154 2 8 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 154 14 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 154 2 6 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 154 (accept_3_3 11 84 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 154 2 5 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 84 154 (Polychromatic418967fa.accept_18_9_12_10_1_387 9 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 154 2 4 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 154 7 1 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 154 2 3 42 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 154 (accept_3_3 5 84 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 154 2 2 42 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 154 (Polychromatic418967fa.accept_20_3_4_14_1_3918 3 84 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 154 2 1 42 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 154
  (Polychromatic418967fa.accept_19_1_8_2_1_2876 1 84 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 83 154 (Eq.refl
  Bool.true) (allA_of_3_1 72 83 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 82 154 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 82 154 2 36 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 154 (accept_3_3 71 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  154 2 35 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 154 (Polychromatic418967fa.accept_19_12_6_2_1_5424 69 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 154 2 34 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 67 82 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 154 2 33 41 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 154 (accept_3_3 65 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 154 2 32 41 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 154
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 63 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 154 2 31 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 154 (Polychromatic418967fa.accept_17_10_14_1_1_5823 61 82 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 154 2 30 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 154 (accept_3_3 59 82 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 154 2 29 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 154 2 28 41 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 154
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 154 2 27 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 154 (accept_3_3 53 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  154 2 26 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 154 (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 154 2 25 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 154 (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 82 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 154 2 24 41 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 154 (accept_3_3 47 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 154 2 23 41 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 154
  (Polychromatic418967fa.accept_13_6_4_11_1_282 45 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 154 2 22 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 154 (Polychromatic418967fa.accept_21_1_19_7_1_1218 43 82 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 154 2 21 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 154 (accept_3_3 41 82 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 154 2 20 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 154 (Polychromatic418967fa.accept_19_1_6_2_1_8341 39 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 154 2 19 41 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 154
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 154 2 18 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 154 (accept_3_3 35 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  154 2 17 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 154 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 154 2 16 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 154 (Polychromatic418967fa.accept_19_12_6_2_1_5424 31 82 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 154 2 15 41 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 154 (accept_3_3 29 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 154 2 14 41 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 154
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 154 2 13 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 154 (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 82 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 154 2 12 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 154 (accept_3_3 23 82 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 154 2 11 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 154 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 154 2 10 41 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 154
  (Polychromatic418967fa.accept_13_6_4_11_1_282 19 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 154 2 9 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 154 (accept_3_3 17 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  154 2 8 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 154 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 154 2 7 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 154 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 82 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 154 2 6 41 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 154 (accept_3_3 11 82 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 154 2 5 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 154 (Polychromatic418967fa.accept_21_9_19_7_1_8376 9 82 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 154 2 4 41 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 154
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 154 2 3 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 154 (accept_3_3 5 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 154
  2 2 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  154 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 82 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 82 154 2 1 41 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 82 154 (Polychromatic418967fa.accept_19_1_6_2_1_8341 1 82 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 81 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 73 81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 154 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 81 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 154 (accept_3_3 71 81 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 154 (Polychromatic418967fa.accept_13_5_3_11_1_1288
  70 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 154
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 69 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 154 (accept_3_3 68 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 154 (accept_3_3 65 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 154 (Polychromatic418967fa.accept_19_7_5_2_1_2842 64 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 154 (accept_3_3 62 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 154 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 154 (accept_3_3 59 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 154 (Polychromatic418967fa.accept_15_13_6_4_1_1221 58 81
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 154
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 154 (accept_3_3 56 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 154 (accept_3_3 53 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 154 (Polychromatic418967fa.accept_19_14_5_2_1_6941 52 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 154 (accept_3_3 50 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 154 (Polychromatic418967fa.accept_17_14_13_1_1_3356 48 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 154 (accept_3_3 47 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 154 (Polychromatic418967fa.accept_13_7_3_11_1_280 46 81 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 154
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 154 (accept_3_3 44 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 154 (accept_3_3 41 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 154 (accept_3_3 38 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 154 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 154 (accept_3_3 35 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 154 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 81
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 154
  (Polychromatic418967fa.accept_13_7_3_11_1_280 33 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 154 (accept_3_3 32 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 154 (accept_3_3 29 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 154 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 154 (accept_3_3 26 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 154 (accept_3_3 23 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 154 (Polychromatic418967fa.accept_19_3_5_2_1_4103 22 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 154
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 154 (accept_3_3 20 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 154 (accept_3_3 17 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 154 (Polychromatic418967fa.accept_19_16_5_2_1_8375 16 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 154 (accept_3_3 14 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 154 (Polychromatic418967fa.accept_17_12_13_1_1_4478 12 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 154 (accept_3_3 11 81 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 154 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 81
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 154
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 154 (accept_3_3 8 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 154 (accept_3_3 5 81 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 154 (Polychromatic418967fa.accept_19_4_5_2_1_8374 4 81 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 154 (accept_3_3 2 81 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 80 154 (Eq.refl
  Bool.true) (allA_of_3_1 75 80 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 79 154 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 154 (accept_3_3 74 79 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 154 (Polychromatic418967fa.accept_13_7_1_11_1_732
  72 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 154 (accept_3_3 71
  79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 154
  (Polychromatic418967fa.accept_27_16_25_19_1_8373 70 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 154 (accept_3_3 68 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 154 (accept_3_3 65 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 154 (accept_3_3 62 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 154 (accept_3_3 59 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 154 (accept_3_3 56 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 154 (Polychromatic418967fa.accept_10_5_9_4_1_1420 55 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 154
  (Polychromatic418967fa.accept_19_16_3_2_1_6964 54 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 154 (accept_3_3 53 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 154 (accept_3_3 50 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 154 (accept_3_3 47 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 154 (Polychromatic418967fa.accept_13_7_1_11_1_732 46 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 154 (accept_3_3 44 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 154 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 154 (accept_3_3 41 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 154 (accept_3_3 38 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 154
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 154 (accept_3_3 35 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 154 (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 154 (accept_3_3 32 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 154 (accept_3_3 29 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 154 (accept_3_3 26 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 154 (accept_3_3 23 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 154 (accept_3_3 20 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 154 (Polychromatic418967fa.accept_24_19_7_10_1_8372 19 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 154 (accept_3_3 17 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 154 (accept_3_3 14 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 154 (accept_3_3 11 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 154 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 154 (accept_3_3 8 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 154 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 79 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 154 (accept_3_3 5 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 154 (accept_3_3 2 79 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 78 154 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 78 154 2 38 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 78 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 154 2 37 39 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 154
  (Polychromatic418967fa.accept_21_10_15_7_1_3784 73 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 78 154 2 36 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 154 (accept_3_3 71 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78
  154 2 35 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  78 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 78 154 2 34 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 78 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 78 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 154 2 33 39 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 154 (accept_3_3 65 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 154 2 32 39 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 154
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 154 2 31 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 78 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 154 2 30 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 154 (accept_3_3 59 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 154 2 29 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 154 2 28 39 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 154
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 55 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 154 2 27 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 154 (accept_3_3 53 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78
  154 2 26 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  78 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 78 154 2 25 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 78 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 154 2 24 39 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 154 (accept_3_3 47 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 154 2 23 39 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 154 2 22 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 154 2 21 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 154 (accept_3_3 41 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 154 2 20 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 154 2 19 39 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 154
  (Polychromatic418967fa.accept_15_7_3_4_1_574 37 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 154 2 18 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 154 (accept_3_3 35 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78
  154 2 17 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  78 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 78 154 2 16 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 78 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 78 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 154 2 15 39 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 154 (accept_3_3 29 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 154 2 14 39 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 154
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 154 2 13 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 154 2 12 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 154 (accept_3_3 23 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 154 2 11 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 154 2 10 39 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 154 2 9 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 154 (accept_3_3 17 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  154 2 8 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 154 2 7 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 78 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 154 2 6 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 154 (accept_3_3 11 78 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 154 2 5 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 78 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 154 2 4 39 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 154 2 3 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 154 (accept_3_3 5 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 154
  2 2 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78
  154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 78 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 154 2 1 39 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 154 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 78 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 154 (allA_of_3_1 77 77
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 154 (allA_succ_of_accept 75 76 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 154 2 37 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 73 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 154 2 36 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 154 (accept_3_3 71 76 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 154 2 35 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 154 2 34 38 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 154 2 33 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 154 (accept_3_3 65 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  154 2 32 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 154 2 31 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 76 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 154 2 30 38 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 154 (accept_3_3 59 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 154 2 29 38 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 154 2 28 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 55 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 154 2 27 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 154 (accept_3_3 53 76 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 154 2 26 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 154 2 25 38 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 154 2 24 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 154 (accept_3_3 47 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  154 2 23 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 154 2 22 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 154 2 21 38 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 154 (accept_3_3 41 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 154 2 20 38 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 154 2 19 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 154 2 18 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 154 (accept_3_3 35 76 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 154 2 17 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 154 2 16 38 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 154 2 15 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 154 (accept_3_3 29 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  154 2 14 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 154 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 154 2 13 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 76 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 154 2 12 38 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 154 (accept_3_3 23 76 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 154 2 11 38 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 154 2 10 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 154 2 9 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 154 (accept_3_3 17 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 154 2 8 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 76 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 154 2 7 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 154 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 154 2 6 38 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 154 (accept_3_3 11
  76 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 154 2 5 38 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 154
  (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 154 2 4 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 154 2 3 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 154 (accept_3_3 5 76 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 154 2 2 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 76 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 154 2 1 38 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  76 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 154 (allA_succ_of_accept
  74 75 154 (accept_3_3 74 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 154 (Polychromatic418967fa.accept_19_15_18_2_1_6857 72 75 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 154 (accept_3_3 71 75 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 69
  75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 154 (accept_3_3 68 75
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 66 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 154 (accept_3_3 65 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 154 (Polychromatic418967fa.accept_13_12_10_11_1_1279 64 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 154 (Polychromatic418967fa.accept_16_15_11_10_1_3639 63 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 154 (accept_3_3 62 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 154 (accept_3_3 59 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 154 (accept_3_3 56 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 154 (accept_3_3 53 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 154 (accept_3_3 50 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 154
  (Polychromatic418967fa.accept_19_10_18_2_1_6936 48 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 154 (accept_3_3 47 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 154 (accept_3_3 44 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 154 (accept_3_3 41 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 154 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 154 (accept_3_3 38 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 154 (accept_3_3 35 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 154 (accept_3_3 32 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 154 (accept_3_3 29 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 154 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 154 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 154 (accept_3_3 26 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 154 (accept_3_3 23 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 154 (accept_3_3 20 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 154 (accept_3_3 17 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 154 (accept_3_3 14 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 154
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 154 (accept_3_3 11 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 154 (Polychromatic418967fa.accept_17_10_7_1_1_7024 10 75 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 154 (accept_3_3 8 75 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 154 (accept_3_3 5 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 75 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 154 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 75 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 154 (accept_3_3 2 75 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 154 (allA_of_3_1 74 74
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 154 (allA_succ_of_accept 72 73 154
  (Polychromatic418967fa.accept_17_4_5_1_1_5776 72 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 154 (accept_3_3 71 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 154 (Polychromatic418967fa.accept_15_10_13_4_1_1210 70 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 154 (accept_3_3 68 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 154
  (Polychromatic418967fa.accept_13_1_8_11_1_724 66 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 154 (accept_3_3 65 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 154 (accept_3_3 62 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 154 (Polychromatic418967fa.accept_13_9_8_11_1_725 61 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 154
  (Polychromatic418967fa.accept_19_3_16_2_1_6837 60 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 154 (accept_3_3 59 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 154 (Polychromatic418967fa.accept_13_6_8_11_1_5398 58 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 154 (accept_3_3 56 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 154
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 54 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 154 (accept_3_3 53 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 154 (accept_3_3 50 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 154 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 154
  (Polychromatic418967fa.accept_13_9_8_11_1_725 48 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 154 (accept_3_3 47 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 154 (Polychromatic418967fa.accept_28_18_17_14_1_8371 46 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 154 (accept_3_3 44 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 154
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 154 (accept_3_3 41 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 154 (accept_3_3 38 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 154 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 154
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 154 (accept_3_3 35 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 154 (Polychromatic418967fa.accept_18_16_1_10_1_2029 34 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 154 (accept_3_3 32 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 154
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 154 (accept_3_3 29 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 154 (accept_3_3 26 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 154 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 154
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 24 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 154 (accept_3_3 23 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 154 (Polychromatic418967fa.accept_13_9_8_11_1_725 22 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 154 (accept_3_3 20 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 154
  (Polychromatic418967fa.accept_19_18_16_2_1_2858 18 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 154 (accept_3_3 17 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 154 (accept_3_3 14 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 154 (Polychromatic418967fa.accept_18_13_1_10_1_4331 13 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 154
  (Polychromatic418967fa.accept_23_12_4_16_1_8370 12 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 154 (accept_3_3 11 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 154 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 154 (accept_3_3 8 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 154
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 154 (accept_3_3 5 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 73 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 154 (accept_3_3 2 73 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 154 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 73 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 154 (allA_succ_of_accept 71
  72 154 (accept_3_3 71 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 154 2 35 36 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 154
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 69 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 154 2 34 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 67 72 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 154 2 33 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 154 (accept_3_3 65 72 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 154 2 32 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 154 (Polychromatic418967fa.accept_19_6_15_2_1_2857 63 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 154 2 31 36 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 154
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 154 2 30 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 154 (accept_3_3 59 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  154 2 29 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 154 2 28 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 154 (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 72 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 154 2 27 36 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 154 (accept_3_3 53 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 154 2 26 36 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 154
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 154 2 25 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 154 (Polychromatic418967fa.accept_19_11_15_2_1_4096 49 72 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 154 2 24 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 154 (accept_3_3 47 72 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 154 2 23 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 154 (Polychromatic418967fa.accept_21_3_9_7_1_8369 45 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 154 2 22 36 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 154
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 154 2 21 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 154 (accept_3_3 41 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  154 2 20 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 154 (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 154 2 19 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 72 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 154 2 18 36 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 154 (accept_3_3 35 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 154 2 17 36 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 154
  (Polychromatic418967fa.accept_23_10_3_16_1_8368 33 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 154 2 16 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 154 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 72 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 154 2 15 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 154 (accept_3_3 29 72 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 154 2 14 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 154 2 13 36 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 154
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 25 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 154 2 12 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 154 (accept_3_3 23 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  154 2 11 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 154 (Polychromatic418967fa.accept_23_21_3_16_1_8367 21 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 154 2 10 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 72 154 (Polychromatic418967fa.accept_21_19_9_7_1_8366 19 72 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 154 2 9 36 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 154 (accept_3_3 17 72 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 154 2 8 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 154 (Polychromatic418967fa.accept_21_15_9_7_1_3780 15 72 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 154 2 7 36 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 154
  (Polychromatic418967fa.accept_19_13_15_2_1_4126 13 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 154 2 6 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 154 (accept_3_3 11 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  154 2 5 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 154 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 154 2 4 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 154 2 3 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 154 (accept_3_3 5 72 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 154 2 2 36 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 154 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 72 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 154 2 1 36 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 154
  (Polychromatic418967fa.accept_13_1_7_11_1_702 1 72 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 154
  (allA_of_3_1 71 71 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 154 (allA_succ_of_accept 69 70 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 154 2 34 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 154 2 33 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 154 (accept_3_3 65 70 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 154 2 32 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 70 154 7 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 70 154 2 31 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 154 (Polychromatic418967fa.accept_20_1_10_14_1_1472 61 70
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 154 2 30 35 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 154 (accept_3_3 59
  70 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 154 2 29 35 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 154 14 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 154 (Polychromatic418967fa.accept_13_3_5_11_1_716 55 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 154 2 27 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 154 (accept_3_3 53 70 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 154 2 26 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 70 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 154 2 25 35 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 70 154 7 7 10 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 70 154 2 24 35 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 154 (accept_3_3 47
  70 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 154 2 23 35 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 154
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 154 2 22 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 154 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 154 14 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 154 (accept_3_3 41 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 70 154 2 20 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 70 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 70 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 154 2 19 35 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 154
  (Polychromatic418967fa.accept_15_7_10_4_1_151 37 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 154 2 18 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 70 154 7 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 70 154 2 17 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 70 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 154 2 16 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 154 2 15 35 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 154 (accept_3_3 29
  70 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 154 14 2 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 154
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 154 2 13 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 154 (Polychromatic418967fa.accept_19_6_13_2_1_8365 25 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 154 2 12 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 154 (accept_3_3 23 70 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 154 2 11 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 154 7 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 154 2 10 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 154 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 70 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 154 2 9 35 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 154 (accept_3_3 17 70 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 154 2 8 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 15
  70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 154 14 1 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 154
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 154 2 6 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 154 (accept_3_3 11 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  154 2 5 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 154 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 154 2 4 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 70 154 7 1 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 70 154 2 3 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 70 154 (accept_3_3 5 70 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 70 154 2 2 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 154 2 1 35 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 154 (Polychromatic418967fa.accept_18_1_16_10_1_2065 1 70 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 154 (allA_succ_of_accept 68 69
  154 (accept_3_3 68 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 154 (accept_3_3 65 69 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 154 (Polychromatic418967fa.accept_13_12_4_11_1_1925 64 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 154 (accept_3_3 62 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 154 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 154 (accept_3_3 59 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 69 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 154 (accept_3_3 56 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 154 (accept_3_3 53 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 154 (accept_3_3 50 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 154 (accept_3_3 47 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 154 (Polychromatic418967fa.accept_13_7_4_11_1_1967 46 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 154
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 154 (accept_3_3 44 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 154 (accept_3_3 41 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 154 (accept_3_3 38 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 154 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 154 (accept_3_3 35 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 69 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 154
  (Polychromatic418967fa.accept_10_3_9_4_1_960 33 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 154 (accept_3_3 32 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 154 (accept_3_3 29 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 154 (accept_3_3 26 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 154 (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 154 (accept_3_3 23 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 69 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 154 (accept_3_3 20 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 154 (accept_3_3 17 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 154 (accept_3_3 14 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 154 (accept_3_3 11 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 154 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 69 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 154
  (Polychromatic418967fa.accept_18_9_15_10_1_395 9 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 154 (accept_3_3 8 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 154 (accept_3_3 5 69 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 69 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 154 (accept_3_3 2 69 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 154 (allA_of_3_1 68 68 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 154 (allA_succ_of_accept 66 67 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 154 (accept_3_3 65 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 154 (accept_3_3 62 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 154 (accept_3_3 59 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 154 (Polychromatic418967fa.accept_18_4_13_10_1_2064 58 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 154 (accept_3_3 56 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 154 (Polychromatic418967fa.accept_13_3_2_11_1_1999 55 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 154
  (Polychromatic418967fa.accept_21_12_4_7_1_8364 54 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 154 (accept_3_3 53 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 154 (accept_3_3 50 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 154 (accept_3_3 47 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 154 (Polychromatic418967fa.accept_17_12_16_1_1_8363 46 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 154 (accept_3_3 44 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 154 (accept_3_3 41 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 154 (accept_3_3 38 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 154
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 154 (accept_3_3 35 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 154 (accept_3_3 32 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 154 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 154 (accept_3_3 29 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 154 (accept_3_3 26 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 154 (accept_3_3 23 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 154 (accept_3_3 20 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 154 (Polychromatic418967fa.accept_17_2_16_1_1_2260 19 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 154
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 154 (accept_3_3 17 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 154 (accept_3_3 14 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 154 (accept_3_3 11 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 154 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 154 (accept_3_3 8 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 154 (accept_3_3 5 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 154 (accept_3_3 2 67 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 154 (allA_succ_of_accept 65 66
  154 (accept_3_3 65 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 154 2 32 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 154
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 154 2 31 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 154 2 30 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 154 (accept_3_3 59 66 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 154 2 29 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 66 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 154 2 28 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 66 154 11 5 6 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 66 154 2 27 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 154 (accept_3_3 53
  66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 154 2 26 33 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 154 2 25 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 66 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 154 2 24 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 154 (accept_3_3 47 66 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 154 2 23 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 154 22 2 3 7 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 154 2 21 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 154 (accept_3_3 41 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66
  154 2 20 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  66 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 66 154 2 19 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 66 154 (Polychromatic418967fa.accept_17_3_15_1_1_3348 37 66 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 154 2 18 33 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 154 (accept_3_3 35 66 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 154 2 17 33 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 154 11 3 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 154 2 16 33 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 154
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 154 2 15 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 154 (accept_3_3 29 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66
  154 2 14 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  66 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 66 154 2 13 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 66 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 154 2 12 33 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 154 (accept_3_3 23 66 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 154 22 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  21 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 154 2 10 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 154
  (Polychromatic418967fa.accept_20_19_6_14_1_3906 19 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 154 2 9 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 154 (accept_3_3 17 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  154 2 8 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 154 2 7 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 154 2 6 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 154 11 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 154 2 5 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9
  66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 154 2 4 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 154 2 3 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 154 (accept_3_3 5 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 154
  2 2 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 154 2 1 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 154 (Polychromatic418967fa.accept_19_1_9_2_1_6945 1 66 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 154 (allA_of_3_1 65 65 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 154 (allA_succ_of_accept 63 64 154
  (Polychromatic418967fa.accept_17_12_13_1_1_4478 63 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 154 2 31 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 64 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 154 2 30 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 154 (accept_3_3 59 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 154 2 29 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 154 (Polychromatic418967fa.accept_21_15_1_7_1_6723 57 64 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 154 2 28 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 154 2 27 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 154 (accept_3_3 53 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  154 2 26 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 154 (Polychromatic418967fa.accept_19_13_7_2_1_5413 51 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 154 2 25 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 64 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 154 2 24 32 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 154 (accept_3_3 47 64 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 154 2 23 32 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 154
  (Polychromatic418967fa.accept_21_3_1_7_1_5187 45 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 154 2 22 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 64 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 154 2 21 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 154 (accept_3_3 41 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 154 2 20 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 154 (Polychromatic418967fa.accept_19_1_7_2_1_4106 39 64 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 154 2 19 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 154 2 18 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 154 (accept_3_3 35 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  154 2 17 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 154 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 154 2 16 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 64 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 64 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 154 2 15 32 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 154 (accept_3_3 29 64 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 154 2 14 32 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 154
  (Polychromatic418967fa.accept_13_1_12_11_1_728 27 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 154 2 13 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 64 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 154 2 12 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 154 (accept_3_3 23 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 154 2 11 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 154 (Polychromatic418967fa.accept_23_21_18_16_1_8362 21 64
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 154 2 10 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 154 2 9 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 154 (accept_3_3 17 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  154 2 8 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 154 (Polychromatic418967fa.accept_21_15_1_7_1_6723 15 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 154 2 7 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 154 2 6 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 154 (accept_3_3 11 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 154 2 5 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 154 (Polychromatic418967fa.accept_19_9_7_2_1_6868 9 64 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 154 2 4 32 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 154 2 3 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 154 (accept_3_3 5 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 154
  2 2 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  154 (Polychromatic418967fa.accept_20_3_4_14_1_3918 3 64 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 64 154 2 1 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 64 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 64 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 154 (allA_succ_of_accept 62 63 154
  (accept_3_3 62 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 154 (Polychromatic418967fa.accept_19_3_6_2_1_6910 60 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 154 (accept_3_3 59 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 154 (Polychromatic418967fa.accept_19_1_6_2_1_8341 58 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 154 7 8 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 154
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 154 (accept_3_3 53 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 154 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 154
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 51 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 154 (accept_3_3 50 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63
  154 7 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  63 154 (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 154 (accept_3_3 47 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 154 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 154 (accept_3_3 44 63 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 154 7 6 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 154 (accept_3_3 41
  63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 154
  (Polychromatic418967fa.accept_17_6_12_1_1_7043 40 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 154 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 154 (accept_3_3 38 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 154 (Polychromatic418967fa.accept_28_8_7_14_1_8361
  36 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 154 7 5 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 154
  (Polychromatic418967fa.accept_19_15_6_2_1_6865 34 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 154 (accept_3_3 32 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 154 (Polychromatic418967fa.accept_12_6_3_10_1_224
  30 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 154 (accept_3_3 29
  63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 154 7 4 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 154
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 154 (accept_3_3 26 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 154 (Polychromatic418967fa.accept_20_4_3_14_1_6813 24 63 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 154 (accept_3_3 23 63 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 154 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 63 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 154 7 3 9 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 154 (accept_3_3 20 63 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 154 (accept_3_3 17 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 154 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 154 (Polychromatic418967fa.accept_17_15_12_1_1_3365 15 63 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 154 7 2 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 154 (Polychromatic418967fa.accept_18_12_9_10_1_3104 12 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 154 (accept_3_3 11 63 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 63 154 (Polychromatic418967fa.accept_19_10_6_2_1_6907 10 63 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 154 (accept_3_3 8 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 154
  7 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 154 (accept_3_3 5 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  154 (Polychromatic418967fa.accept_19_4_6_2_1_6906 4 63 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 154 (Polychromatic418967fa.accept_19_3_6_2_1_6910 3 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 154 (accept_3_3 2 63 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 154 (allA_of_3_1 62 62 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 154 (allA_succ_of_accept 60 61 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 154 (accept_3_3 59 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 154 (accept_3_3 56 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 154
  (Polychromatic418967fa.accept_13_2_9_11_1_258 54 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 154 (accept_3_3 53 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 154 (accept_3_3 50 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 154 (accept_3_3 47 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 154 (Polychromatic418967fa.accept_13_7_9_11_1_705 46 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 154 (accept_3_3 44 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 154 (accept_3_3 41 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 154 (accept_3_3 38 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 154 (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 154
  (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 154 (accept_3_3 35 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 154 (Polychromatic418967fa.accept_13_8_9_11_1_1265 34 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 154 (accept_3_3 32 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 154 (accept_3_3 29 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 154 (accept_3_3 26 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 154 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 154 (accept_3_3 23 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 154 (accept_3_3 20 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 154
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 154 (accept_3_3 17 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 154 (accept_3_3 14 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 154 (accept_3_3 11 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 154 (Polychromatic418967fa.accept_20_10_1_14_1_8359 10 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 154 (accept_3_3 8 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 154 (accept_3_3 5 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 154 (accept_3_3 2 61 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 154 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 61 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 154 (allA_succ_of_accept 59 60 154 (accept_3_3 59 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 154 2 29 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 154 2 28 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 154 (Polychromatic418967fa.accept_13_3_8_11_1_1906
  55 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 154 2 27 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 154 (accept_3_3 53
  60 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 154 2 26 30 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 154
  (Polychromatic418967fa.accept_16_3_12_10_1_315 51 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 154 2 25 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 154 2 24 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 154 (accept_3_3 47 60 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 154 2 23 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 154 (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 60 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 154 2 22 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 154 2 21 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 154 (accept_3_3 41 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  154 2 20 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 154 2 19 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 154 (Polychromatic418967fa.accept_16_5_12_10_1_3508 37 60 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 154 2 18 30 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 154 (accept_3_3 35 60 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 154 2 17 30 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 154
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 33 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 154 2 16 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 154 2 15 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 154 (accept_3_3 29 60 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 154 2 14 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 154 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 60 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 154 2 13 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 154
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 154 2 12 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 154 (accept_3_3 23 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60
  154 2 11 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  60 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 60 154 2 10 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 60 154 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 60 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 154 2 9 30 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 154 (accept_3_3 17 60 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 154 2 8 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 154 (Polychromatic418967fa.accept_17_15_9_1_1_3363 15 60 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 154 2 7 30 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 154
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 154 2 6 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 154 (accept_3_3 11 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  154 2 5 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 154 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 154 2 4 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 154 2 3 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 154 (accept_3_3 5 60 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 154 2 2 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 154 2 1 30 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 154
  (Polychromatic418967fa.accept_13_1_8_11_1_724 1 60 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 154 (allA_of_3_1 59 59 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 154 (allA_succ_of_accept 57 58 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 154 2 28 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 154 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 154 2 27 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 154 (accept_3_3 53 58 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 154 2 26 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 58 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 154 2 25 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 154 2 24 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 154 (accept_3_3 47 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  154 2 23 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 154 (Polychromatic418967fa.accept_17_11_7_1_1_7023 45 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 154 2 22 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 154 2 21 29 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 154 (accept_3_3 41 58 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 154 2 20 29 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 154 2 19 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 154 (Polychromatic418967fa.accept_19_18_1_2_1_5430 37 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 154 2 18 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 154 (accept_3_3 35 58 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 154 2 17 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 58 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 154 2 16 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 154
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 154 2 15 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 154 (accept_3_3 29 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  154 2 14 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 154 (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 154 2 13 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 154 2 12 29 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 154 (accept_3_3 23 58 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 154 2 11 29 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 154 2 10 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 154 2 9 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 154 (accept_3_3 17 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 154 2 8 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 58 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 154 2 7 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 154 (Polychromatic418967fa.accept_18_13_4_10_1_1076
  13 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 154 2 6 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 154 (accept_3_3 11
  58 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 154 2 5 29 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 154 2 4 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 154 2 3 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 154 (accept_3_3 5 58 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 154 2 2 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 58 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 154 2 1 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 154 (Polychromatic418967fa.accept_21_1_16_7_1_3763 1
  58 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 154 (allA_succ_of_accept 56 57 154
  (accept_3_3 56 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 57 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 154 (accept_3_3 53 57 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 154 (accept_3_3 50 57
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 154 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 154
  (Polychromatic418967fa.accept_25_23_7_4_1_8358 48 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 154 (accept_3_3 47 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 154 (Polychromatic418967fa.accept_13_7_5_11_1_1927 46 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 154 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 154 (accept_3_3 44 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 154 (accept_3_3 41 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 154 (accept_3_3 38 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 154
  (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 154 (accept_3_3 35 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 154 (accept_3_3 32 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 154 (accept_3_3 29 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 154 (Polychromatic418967fa.accept_23_5_11_16_1_6597 28 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 154 (accept_3_3 26 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 154 (accept_3_3 23 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 154 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 154 (accept_3_3 20 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 154 (accept_3_3 17 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 154 (accept_3_3 14 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 154
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 154 (accept_3_3 11 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 154 (Polychromatic418967fa.accept_21_10_15_7_1_3784 10 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 154 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 154 (accept_3_3 8 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 154 (accept_3_3 5 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 57 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 154 (accept_3_3 2 57 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 154)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 154 (allA_of_3_1 56 56 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 154
  (allA_succ_of_accept 54 55 154 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 55 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 154 (accept_3_3 53 55 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 154 (accept_3_3 50 55
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 154
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 48 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 154 (accept_3_3 47 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 55 154 11 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 154 (Polychromatic418967fa.accept_15_13_10_4_1_1232
  43 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 154
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 42 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 154 (accept_3_3 41 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 154 (accept_3_3 38 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 154 (accept_3_3 35 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 154 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 55 154 11 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 55 154 (accept_3_3 32 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 55 154 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 55 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 154 (Polychromatic418967fa.accept_16_14_7_10_1_898 30 55
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 154 (accept_3_3 29 55 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 154 (Polychromatic418967fa.accept_12_4_7_10_1_563
  28 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 154 (accept_3_3 26 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 154 (Polychromatic418967fa.accept_15_9_10_4_1_2055 24 55 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 154 (accept_3_3 23 55 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 154 11 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 154 (accept_3_3 20 55 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 154 (Polychromatic418967fa.accept_10_9_5_4_1_966
  19 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 154
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 154 (accept_3_3 17 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 154 (accept_3_3 14 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 154
  (Polychromatic418967fa.accept_19_12_17_2_1_6888 12 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 55 154 11 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 154 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 55 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 154 (accept_3_3 8 55 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 154 (Polychromatic418967fa.accept_13_7_3_11_1_280 7
  55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 154
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 154 (accept_3_3 5 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 55 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 154 (accept_3_3 2 55 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 154 (allA_succ_of_accept 53 54 154
  (accept_3_3 53 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 154 2 26 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 154
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 154 2 25 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 154 (Polychromatic418967fa.accept_13_10_2_11_1_1920 49 54 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 154 2 24 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 154 (accept_3_3 47 54 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 154 2 23 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 54 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 154 2 22 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 154
  (Polychromatic418967fa.accept_13_4_2_11_1_733 43 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 154 2 21 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 154 (accept_3_3 41 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  154 2 20 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 154 2 19 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 154 (Polychromatic418967fa.accept_19_18_16_2_1_2858 37 54 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 154 2 18 27 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 154 (accept_3_3 35 54 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 154 2 17 27 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 154 2 16 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 154 (Polychromatic418967fa.accept_28_3_26_14_1_8356 31 54 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 154 2 15 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 154 (accept_3_3 29 54 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 154 2 14 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 154 2 13 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 154
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 154 2 12 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 154 (accept_3_3 23 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  154 2 11 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 154 2 10 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 154 (Polychromatic418967fa.accept_17_2_3_1_1_2244 19 54 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 154 2 9 27 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 154 (accept_3_3 17 54 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 154 2 8 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 54 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 154 2 7 27 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 154
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 154 2 6 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 154 (accept_3_3 11 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  154 2 5 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 154 2 4 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 154 (Polychromatic418967fa.accept_19_7_16_2_1_6953 7 54 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 154 2 3 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 154 (accept_3_3 5 54 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 154 2 2 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 154 2 1 27 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 154
  (Polychromatic418967fa.accept_21_1_12_7_1_3783 1 54 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 154)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 154 (allA_of_3_1 53 53 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 154 (allA_succ_of_accept 51 52 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 154 2 25 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 154 2 24 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 154 (accept_3_3 47 52 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 154 2 23 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 154 (Polychromatic418967fa.accept_19_7_14_2_1_4095 45 52 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 154 2 22 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 154 2 21 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 154 (accept_3_3 41 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  154 2 20 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 154 2 19 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 52 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 154 2 18 26 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 154 (accept_3_3 35 52 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 154 2 17 26 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 154 2 16 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 154 2 15 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 154 (accept_3_3 29 52 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 154 2 14 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 52 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 154 2 13 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 154 2 12 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 154 (accept_3_3 23 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  154 2 11 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 154 2 10 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 52 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 154 2 9 26 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 154 (accept_3_3 17 52 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 154 2 8 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 52 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 154 2 7 26 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 154
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 154 2 6 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 154 (accept_3_3 11 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  154 2 5 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 154 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 154 2 4 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 154 2 3 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 154 (accept_3_3 5 52 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 154 2 2 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 154 2 1 26 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 52 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 154)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 154 (allA_succ_of_accept 50 51 154
  (accept_3_3 50 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 154 (accept_3_3 47 51 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 154 (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 154 (accept_3_3 44 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 154 (accept_3_3 41 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 154 (accept_3_3 38 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 154 (accept_3_3 35 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 51 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 154 (accept_3_3 32 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 154 (accept_3_3 29 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 154 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 154
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 154 (accept_3_3 26 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 154 (accept_3_3 23 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 154 (accept_3_3 20 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 154 (accept_3_3 17 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 154
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 154 (accept_3_3 14 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 154 (accept_3_3 11 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 51 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 154 (accept_3_3 8 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 154 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 51 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 154 (accept_3_3 5 51 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 51 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 154 (accept_3_3 2 51 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  154))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 154 (allA_of_3_1 50 50 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 154 (allA_succ_of_accept 48 49 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 154 (accept_3_3 47 49 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 154
  (Polychromatic418967fa.accept_17_12_15_1_1_5798 46 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 154 (accept_3_3 44 49 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 49 154 7 6 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 49 154 (accept_3_3 41 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 154 (accept_3_3 38 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 154 (Polychromatic418967fa.accept_17_3_15_1_1_3348 37 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 154 (Polychromatic418967fa.accept_23_13_3_16_1_8355 36 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 49 154 7 5 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 49 154
  (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 49 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 154 (accept_3_3 32 49 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 49 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 30
  49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 154 (accept_3_3 29 49
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 154 7 4 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 49 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 154 (accept_3_3 26 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 154 (accept_3_3 23 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 154 (Polychromatic418967fa.accept_18_4_13_10_1_2064 22 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 154 7 3 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 154 (accept_3_3 20 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 154 (accept_3_3 17 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 154 7 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 154 (Polychromatic418967fa.accept_10_3_9_4_1_960 13
  49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 154 (accept_3_3 11 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 154 (Polychromatic418967fa.accept_19_10_11_2_1_8354 10 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 154 (accept_3_3 8 49 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 154 7 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 49 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 154 (accept_3_3 5 49 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 154 (accept_3_3 2 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  154 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 49 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 154))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 154 (allA_succ_of_accept
  47 48 154 (accept_3_3 47 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 154 2 23 24 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 154
  (Polychromatic418967fa.accept_18_9_12_10_1_387 45 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 154 2 22 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 154 2 21 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 154 (accept_3_3 41 48 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 154 2 20 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 154 2 19 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 154
  (Polychromatic418967fa.accept_15_7_3_4_1_574 37 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 154 2 18 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 154 (accept_3_3 35 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  154 2 17 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 154 2 16 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 48 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 154 2 15 24 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 154 (accept_3_3 29 48 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 154 2 14 24 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 154
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 154 2 13 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 154 2 12 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 154 (accept_3_3 23 48 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 154 2 11 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 154 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 154 2 10 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 154 2 9 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 154 (accept_3_3 17 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  154 2 8 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 154 2 7 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 154 2 6 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 154 (accept_3_3 11 48 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 154 2 5 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 48 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 48 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 154 2 4 24 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 154
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 154 2 3 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 154 (accept_3_3 5 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 154
  2 2 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48
  154 (Polychromatic418967fa.accept_20_3_8_14_1_5342 3 48 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 48 154 2 1 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 48 154 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 48 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 154)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 154 (allA_of_3_1 47 47 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 154 (allA_succ_of_accept 45 46
  154 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 154 2 22 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 154 (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 46 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 154 2 21 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 154 (accept_3_3 41 46 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 154 2 20 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 154 (Polychromatic418967fa.accept_16_7_14_10_1_3544 39 46
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 154 2 19 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 154
  (Polychromatic418967fa.accept_16_5_14_10_1_3644 37 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 154 2 18 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 154 (accept_3_3 35 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  154 2 17 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 154 (Polychromatic418967fa.accept_15_3_1_4_1_1246 33 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 154 2 16 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 154 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 46 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 154 2 15 23 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 154 (accept_3_3 29 46 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 154 2 14 23 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 154
  (Polychromatic418967fa.accept_13_1_7_11_1_702 27 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 154 2 13 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 46 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 154 2 12 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 154 (accept_3_3 23 46 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 154 2 11 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 154 (Polychromatic418967fa.accept_16_5_14_10_1_3644 21 46
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 154 2 10 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 154
  (Polychromatic418967fa.accept_20_19_6_14_1_3906 19 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 154 2 9 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 154 (accept_3_3 17 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  154 2 8 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 154 2 7 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 154 (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 46 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 154 2 6 23 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 154 (accept_3_3 11 46 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 154 2 5 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 154 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 46 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 154 2 4 23 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 154
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 154 2 3 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 154 (accept_3_3 5 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 154
  2 2 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  154 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 46 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 46 154 2 1 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 46 154 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 46 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 154)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  154 (allA_succ_of_accept 44 45 154 (accept_3_3 44 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 45 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 154 (accept_3_3 41 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 154 (Polychromatic418967fa.accept_23_17_22_16_1_8353 40 45 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 154 (accept_3_3 38 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 154 (accept_3_3 35 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 154 (Polychromatic418967fa.accept_13_8_6_11_1_1979 34 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 154
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 154 (accept_3_3 32 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 154 (accept_3_3 29 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 154 (Polychromatic418967fa.accept_16_12_13_10_1_2637 28 45 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 154 (accept_3_3 26 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 154 (Polychromatic418967fa.accept_17_7_11_1_1_4503 24 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 154 (accept_3_3 23 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 154 (Polychromatic418967fa.accept_21_1_3_7_1_3727 22 45 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 154
  (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 154 (accept_3_3 20 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 154 (accept_3_3 17 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 154 (accept_3_3 14 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 154 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 154 (accept_3_3 11 45 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 154 (Polychromatic418967fa.accept_17_10_11_1_1_5784 10 45
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 154
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 154 (accept_3_3 8 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 154 (accept_3_3 5 45 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 154 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 45 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 154 (accept_3_3 2 45 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  154))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 154 (allA_of_3_1 44 44 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 154 (allA_succ_of_accept 42 43 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 154 (accept_3_3 41 43 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 40
  43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 154 (accept_3_3 38 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 154 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 154 (accept_3_3 35 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 154 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 43
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 154 (accept_3_3 32 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 154 (accept_3_3 29 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 154 (accept_3_3 26 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 154 (accept_3_3 23 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 154 (accept_3_3 20 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 154 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 154 (Polychromatic418967fa.accept_19_18_5_2_1_8352 18 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 154 (accept_3_3 17 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 154 (accept_3_3 14 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 154 (accept_3_3 11 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 154 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 43 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 154 (accept_3_3 8 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  154 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 43 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 154 (accept_3_3 5 43 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 154 (accept_3_3 2 43 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  154))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 154 (allA_succ_of_accept 41 42 154 (accept_3_3 41 42 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 154 2 20 21 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 154 2 19 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 42 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 154 2 18 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 154 7 5 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 154 2 17 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  33 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 154 2 16 21 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 154
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 154 2 15 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 154 (accept_3_3 29 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  154 14 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 154 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 154 2 13 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 154 2 12 21 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 154 (accept_3_3 23 42 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 154 2 11 21 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 154 7 3 6 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 154 2 10 21 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 154
  (Polychromatic418967fa.accept_24_19_18_10_1_8351 19 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 42 154 2 9 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 42 154 (accept_3_3 17 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 154 2 8 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 42 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 154 14 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 154 2 6 21 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 154 (accept_3_3 11 42 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 154 2 5 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 154 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9
  42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 154 2 4 21 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 154 7 1 6 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 154 2 3 21 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 154 (accept_3_3 5 42
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 154 2 2 21 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 154 2 1 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 154 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 42 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 154)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 154
  (allA_of_3_1 41 41 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 154 (allA_succ_of_accept 39 40 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 154 2 19 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 40 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 154 2 18 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 154 (accept_3_3 35 40 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 154 2 17 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 154 2 16 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 154
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 154 2 15 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 154 (accept_3_3 29 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  154 2 14 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 154 (Polychromatic418967fa.accept_24_3_16_10_1_8350 27 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 154 2 13 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 40 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 154 2 12 20 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 154 (accept_3_3 23 40 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 154 2 11 20 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 154 2 10 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 154 2 9 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 154 (accept_3_3 17 40 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 154 2 8 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 40 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 154 2 7 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 154 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 154 2 6 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 154 (accept_3_3 11
  40 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 154 2 5 20 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 154
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 154 2 4 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 154 2 3 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 154 (accept_3_3 5 40 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 154 2 2 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 154 2 1 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  40 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  154)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 154 (allA_succ_of_accept 38 39 154 (accept_3_3 38 39 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 154
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 154 (accept_3_3 35 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 154 (accept_3_3 32 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 154 (accept_3_3 29 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 154 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 154 (accept_3_3 26 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 154 (accept_3_3 23 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 154 (accept_3_3 20 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 154
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 154 (accept_3_3 17 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 154 (accept_3_3 14 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 154
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 154 (accept_3_3 11 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 154 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 154 (accept_3_3 8 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 154
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 154 (accept_3_3 5 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 154 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 39 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 154 (accept_3_3 2 39 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 154))))))))))))))))))))))))))))))))))))))) (allB_succ 38 154
  (allA_of_3_1 38 38 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 154 (allA_succ_of_accept 36 37 154
  (Polychromatic418967fa.accept_17_2_3_1_1_2244 36 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 154 (accept_3_3 35 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 154 (Polychromatic418967fa.accept_18_16_1_10_1_2029 34 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 154 (accept_3_3 32 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 154
  (Polychromatic418967fa.accept_16_14_5_10_1_3622 30 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 154 (accept_3_3 29 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 154 (accept_3_3 26 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 154 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 154
  (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 154 (accept_3_3 23 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 154 (accept_3_3 20 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 154
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 154 (accept_3_3 17 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 154 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 154 (accept_3_3 14 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 154 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 154
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 154 (accept_3_3 11 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 154 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 154 (accept_3_3 8 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 154
  (Polychromatic418967fa.accept_17_6_3_1_1_7011 6 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 154 (accept_3_3 5 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 37 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 154 (accept_3_3 2 37 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 154 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 37 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 154))))))))))))))))))))))))))))))))))))) (allB_succ
  36 154 (allA_succ_of_accept 35 36 154 (accept_3_3 35 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  34 36 154 2 17 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 154 (Polychromatic418967fa.accept_17_16_2_1_1_4492 33 36 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 154 2 16 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 154 (Polychromatic418967fa.accept_19_12_17_2_1_6888
  31 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 154 2 15 18 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 154 (accept_3_3 29
  36 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 154 2 14 18 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 154
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 154 2 13 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 36 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 154 2 12 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 154 (accept_3_3 23 36 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 154 2 11 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 154 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 36
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 154 2 10 18 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 154
  (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 154 2 9 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 154 (accept_3_3 17 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  154 2 8 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 154 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 154 2 7 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 154 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 36 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 154 2 6 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 154 (accept_3_3 11 36 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 154 2 5 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 154 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 36 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 154 2 4 18 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 154
  (Polychromatic418967fa.accept_19_7_17_2_1_6855 7 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 154 2 3 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 154 (accept_3_3 5 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 154
  2 2 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  154 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 36 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 36 154 2 1 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 36 154 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 36 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 154)))))))))))))))))))))))))))))))))))) (allB_succ 35 154
  (allA_of_3_1 35 35 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 154 (allA_succ_of_accept 33 34 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 154 2 16 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 154 2 15 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 154 (accept_3_3 29 34 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 154 2 14 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 154 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 34 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 154 2 13 17 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 154
  (Polychromatic418967fa.accept_19_6_15_2_1_2857 25 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 154 2 12 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 154 (accept_3_3 23 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  154 2 11 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 154 2 10 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 154 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 34 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 154 2 9 17 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 154 (accept_3_3 17 34 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 154 2 8 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 154 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 34 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 154 2 7 17 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 154
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 154 2 6 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 154 (accept_3_3 11 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  154 2 5 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 154 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 154 2 4 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 154 (Polychromatic418967fa.accept_23_7_11_16_1_8349 7 34 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 154 2 3 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 154 (accept_3_3 5 34 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 154 2 2 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 154 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 34 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 154 2 1 17 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 154
  (Polychromatic418967fa.accept_13_1_8_11_1_724 1 34 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 154)))))))))))))))))))))))))))))))))) (allB_succ 33 154 (allA_succ_of_accept 32 33 154 (accept_3_3 32 33
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 154 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 154 (accept_3_3 29 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 154 (Polychromatic418967fa.accept_20_8_13_14_1_5321 28 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 154 (accept_3_3 26 33 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 154
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 154 (accept_3_3 23 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33
  154 11 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  33 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 154 (accept_3_3 20 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 154 (accept_3_3 17 33 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 16
  33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 154 (accept_3_3 14 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 33 154 11 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 154 (Polychromatic418967fa.accept_25_10_8_4_1_8348
  10 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 154
  (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 154 (accept_3_3 8 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 154 (accept_3_3 5 33 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 33 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 154 (accept_3_3 2 33 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 154)))))))))))))))))))))))))))))))))
  (allB_succ 32 154 (allA_of_3_1 32 32 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 154
  (allA_succ_of_accept 30 31 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 154 (accept_3_3 29 31 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 154 (accept_3_3 26 31
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 154 (Polychromatic418967fa.accept_4_1_3_2_1_3
  25 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 154 (accept_3_3 23 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 154 (Polychromatic418967fa.accept_18_4_13_10_1_2064 22 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 154 (accept_3_3 20 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 154 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 31 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 154
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 154 (accept_3_3 17 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 154 (accept_3_3 14 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 154 (accept_3_3 11 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 154 (Polychromatic418967fa.accept_17_10_14_1_1_5823 10 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 154 (accept_3_3 8 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 154 (accept_3_3 5 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 154 (accept_3_3 2 31 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 154))))))))))))))))))))))))))))))) (allB_succ 30 154
  (allA_succ_of_accept 29 30 154 (accept_3_3 29 30 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  154 2 14 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 154 2 13 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 30 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 154 2 12 15 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 154 (accept_3_3 23 30 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 154 2 11 15 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 154 2 10 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 154 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 30 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 154 2 9 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 154 (accept_3_3 17 30 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 154 2 8 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 154 2 7 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  30 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 154 2 6 15 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 154 (accept_3_3 11
  30 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 154 2 5 15 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 154
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 154 2 4 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 154 2 3 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 154 (accept_3_3 5 30 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 154 2 2 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 30 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 154 2 1 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 154 (Polychromatic418967fa.accept_20_1_10_14_1_1472
  1 30 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 154))))))))))))))))))))))))))))))
  (allB_succ 29 154 (allA_of_3_1 29 29 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 154
  (allA_succ_of_accept 27 28 154 (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 28 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 154 2 13 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 154 (Polychromatic418967fa.accept_12_1_4_10_1_209
  25 28 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 154 2 12 14 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 154 (accept_3_3 23
  28 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 154 2 11 14 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 28 154 7 3 4 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 28 154 2 10 14 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 154
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 154 2 9 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 154 (accept_3_3 17 28 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  154 2 8 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 154 (Polychromatic418967fa.accept_19_15_9_2_1_8347 15 28 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 154 14 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 28 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 154 2 6 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 154 (accept_3_3 11 28 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 154 2 5 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 154 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 154 2 4 14 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 28 154 7 1 4 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 28 154 2 3 14 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 154 (accept_3_3 5 28 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 154 2 2 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 154 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 28 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 154 2 1 14 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 28 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 154)))))))))))))))))))))))))))) (allB_succ 27 154 (allA_succ_of_accept 26 27 154 (accept_3_3 26 27 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 154
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 154 (accept_3_3 23 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 154 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 154 (accept_3_3 20 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 154 (accept_3_3 17 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 154 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 154 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 27 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 154 (accept_3_3 14 27 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 154
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 154 (accept_3_3 11 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 154 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 154 (accept_3_3 8 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 154
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 154 (accept_3_3 5 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  154 (Polychromatic418967fa.accept_21_4_6_7_1_3693 4 27 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 154 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 154 (accept_3_3 2 27 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 154))))))))))))))))))))))))))) (allB_succ 26 154
  (allA_of_3_1 26 26 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 154 (allA_succ_of_accept 24 25 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 154 (accept_3_3 23 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 154 (accept_3_3 20 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 154
  (Polychromatic418967fa.accept_21_18_4_7_1_8346 18 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 154 (accept_3_3 17 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 154 (accept_3_3 14 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 154 (accept_3_3 11 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 154 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 154 (accept_3_3 8 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 154 (accept_3_3 5 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  154 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 154 (accept_3_3 2 25 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 154 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 25 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 154))))))))))))))))))))))))) (allB_succ 24 154
  (allA_succ_of_accept 23 24 154 (accept_3_3 23 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  154 2 11 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 154 2 10 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 24 154 (Polychromatic418967fa.accept_20_19_4_14_1_8345 19 24 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 154 2 9 12 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 154 (accept_3_3 17 24 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 154 2 8 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 154 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 24
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 154 2 7 12 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 154
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 154 2 6 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 154 (accept_3_3 11 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  154 2 5 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 154 (Polychromatic418967fa.accept_20_9_4_14_1_8344 9 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 154 2 4 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 154 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 154 2 3 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 154 (accept_3_3 5 24 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 154 2 2 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 154 2 1 12 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 154
  (Polychromatic418967fa.accept_21_1_3_7_1_3727 1 24 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 154)))))))))))))))))))))))) (allB_succ 23 154 (allA_of_3_1 23 23 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 154 (allA_succ_of_accept 21 22 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 154 2 10 11 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 154
  (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 22 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 154 2 9 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 154 (accept_3_3 17 22 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  154 2 8 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 154 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 154 2 7 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 154 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 22 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 154 2 6 11 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 154 11 1 2 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 154 2 5 11 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 154
  (Polychromatic418967fa.accept_25_9_22_4_1_8343 9 22 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 154 2 4 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 154 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 154 2 3 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 154 (accept_3_3 5 22 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 154 2 2 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 22 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 154 2 1 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 154 (Polychromatic418967fa.accept_13_1_9_11_1_703 1
  22 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 154)))))))))))))))))))))) (allB_succ
  21 154 (allA_succ_of_accept 20 21 154 (accept_3_3 20 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 154 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 154 (accept_3_3 17 21 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  21 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 154 7 2 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 154 (Polychromatic418967fa.accept_16_12_5_10_1_3561 12 21
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 154 (accept_3_3 11 21 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 154
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 21 154 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 21 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 154 (accept_3_3 8 21 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 21 154 7 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 21 154 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 154 (accept_3_3 5 21 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 154 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 154
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 154 (accept_3_3 2 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21
  154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 154))))))))))))))))))))) (allB_succ 20 154 (allA_of_3_1 20 20 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 19 154 (allA_succ_of_accept 18 19 154 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 154 (accept_3_3 17 19 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 154 (Polychromatic418967fa.accept_12_4_7_10_1_563
  16 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 154 (accept_3_3 14 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 154 (Polychromatic418967fa.accept_16_12_3_10_1_3524 12 19 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 154 (accept_3_3 11 19 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 154 (Polychromatic418967fa.accept_21_10_19_7_1_3719 10 19
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 154 (accept_3_3 8 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  154 (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 19 154 (Polychromatic418967fa.accept_17_6_2_1_1_3350 6 19 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 154 (accept_3_3 5 19 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 154 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 19 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 154
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 154 (accept_3_3 2 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 154))))))))))))))))))) (allB_succ 18 154 (allA_succ_of_accept 17 18 154 (accept_3_3 17 18 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 154 2 8 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 18 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 154 2 7 9 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 154
  (Polychromatic418967fa.accept_21_13_18_7_1_1216 13 18 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 154 2 6 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 154 (accept_3_3 11 18 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18
  154 2 5 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18
  154 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 18 154 2 4 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 154 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 18 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 154 2 3 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 154 (accept_3_3 5 18 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 18 154 2 2 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 18 154 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 18 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 154 2 1 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 154 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1
  18 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 154)))))))))))))))))) (allB_succ 17
  154 (allA_of_3_1 17 17 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 154 (allA_succ_of_accept 15 16 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 16 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 154 2 7 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 154 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 154 2 6 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 154 (accept_3_3 11 16 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 154 2 5 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 154 (Polychromatic418967fa.accept_21_9_16_7_1_5222 9 16 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 154 2 4 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 154 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 154 2 3 8 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 154 (accept_3_3 5 16
  154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 154 2 2 8 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 154
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 16 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 154 2 1 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 154 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 16 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 154)))))))))))))))) (allB_succ 15 154 (allA_succ_of_accept 14 15 154
  (accept_3_3 14 15 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 154 (accept_3_3 11 15 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 154 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 15 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 154
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 154 (accept_3_3 8 15 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  154 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 154 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 154 (accept_3_3 5 15 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 154 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 15 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 154 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 154 (accept_3_3 2 15 154
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15
  154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 154))))))))))))))) (allB_succ 14 154
  (allA_of_3_1 14 14 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 154 (allA_succ_of_accept 12 13 154
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 154 (accept_3_3 11 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 154 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 154 (accept_3_3 8 13 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 154
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 154 (accept_3_3 5 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  154 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 13 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 154 (accept_3_3 2 13 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 154 (Polychromatic418967fa.accept_18_1_13_10_1_2024 1 13 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 154))))))))))))) (allB_succ 12 154
  (allA_succ_of_accept 11 12 154 (accept_3_3 11 12 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  154 2 5 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  154 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 12 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 154 2 4 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 154 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 154 2 3 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 154 (accept_3_3 5 12 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 154 2 2 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 154 (Polychromatic418967fa.accept_16_3_12_10_1_315 3 12 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 154 2 1 6 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 154
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 12 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 154)))))))))))) (allB_succ 11 154 (allA_of_3_1 11 11 154 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 154 (allA_succ_of_accept 9 10 154 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 10 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 154 2 4 5 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 154
  (Polychromatic418967fa.accept_15_7_10_4_1_151 7 10 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 154 2 3 5 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 154 (accept_3_3 5 10 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 154
  2 2 5 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 154
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 10 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 154 2 1 5 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 154 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 10 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 154)))))))))) (allB_succ 9 154 (allA_succ_of_accept 8 9 154 (accept_3_3 8
  9 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 154 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 9 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 154
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 154 (accept_3_3 5 9 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 154
  (Polychromatic418967fa.accept_19_4_9_2_1_8342 4 9 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 154 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 154 (accept_3_3 2 9 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 154 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 154))))))))) (allB_succ 8 154 (allA_of_3_1 8 8 154 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 154 (allA_succ_of_accept 6 7 154
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 154 (accept_3_3 5 7 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 154
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 154 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 154 (accept_3_3 2 7 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 154))))))) (allB_succ 6 154 (allA_succ_of_accept 5 6 154
  (accept_3_3 5 6 154 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 154 2 2 3 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 154
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 154 2 1 3 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 154 (Polychromatic418967fa.accept_19_1_6_2_1_8341 1 6 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 154)))))) (allB_succ 5 154 (allA_of_3_1 5 5 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 154 (allA_succ_of_accept 3 4 154 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 154
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 154 2 1 2 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 154
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 4 154 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 154)))) (allB_succ 3 154 (allA_succ_of_accept 2 3 154 (accept_3_3 2 3 154 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 154 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 154))) (allB_succ 2 154 (allA_of_3_1 2 2 154 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  154))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


