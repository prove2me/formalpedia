-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch176
-- name    : Polychromatic418967fa_Branch176
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:49.405778+00:00
-- url     : https://prove2.me/theorems/640d556c-2f1f-4047-82a7-b7cdd7f5ad98
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

def Polychromatic418967fa.branch_176 : allB 176 176 :=
  allB_succ' 2 175 176 (Eq.refl Bool.true) (allA_of_3_0 2 175 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  174 176 (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 176 2 1 87 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 176 (accept_3_2 1 174 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 176))) (allB_succ' 4 173 176 (Eq.refl Bool.true) (allA_succ_of_accept 3 173 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 173 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 173 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 176 (accept_3_2 1 173 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 173 176)))) (allB_succ' 5 172 176 (Eq.refl Bool.true) (allA_of_3_0 5 172 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 171 176 (Eq.refl Bool.true) (allA_succ_of_accept 5 171 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 176 (accept_3_2 4 171 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 171 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 171 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 176 (accept_3_2 1 171 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 176)))))) (allB_succ' 7 170 176 (Eq.refl Bool.true) (allA_succ_of_gcd 6 170 176 2 3
  85 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 170 176
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 170 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 170 176 2 2 85 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 170 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 170 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 176 2 1 85 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 176 (accept_3_2 1 170 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 170 176))))))) (allB_succ' 8 169 176 (Eq.refl Bool.true) (allA_of_3_0 8 169 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 168 176 (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 176 8 1 21 22
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 176
  (accept_3_2 7 168 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 176 2 3 84 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 176
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 168 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 176 4 1 42 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 176 2 1 84 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 176 (accept_3_2 1 168 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 176))))))))) (allB_succ' 10 167 176 (Eq.refl Bool.true) (allA_succ_of_accept 9 167 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 167 176 (Polychromatic418967fa.accept_17_8_14_6_1_8727 8 167 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 176 (accept_3_2 7 167 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 167 176 (Polychromatic418967fa.accept_15_6_2_11_1_325 6 167 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  167 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 176 (accept_3_2 4 167
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 167 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 167 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 176 (accept_3_2 1 167 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  176)))))))))) (allB_succ' 11 166 176 (Eq.refl Bool.true) (allA_of_3_0 11 166 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 165 176 (Eq.refl Bool.true) (allA_succ_of_gcd 11 165 176 11 1 15 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 165 176 (accept_3_2 10 165 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 9
  165 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 165 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 176 (accept_3_2 7 165 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 165 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 176 (accept_3_2 4 165 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 165 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 176 (accept_3_2 1 165 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  176)))))))))))) (allB_succ' 13 164 176 (Eq.refl Bool.true) (allA_succ_of_gcd 12 164 176 4 3 41 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 164 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 176 2 5 82 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 164 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 164 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 176 4 2 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 176 (accept_3_2 7 164 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 164 176 2 3 82 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 164 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 176 4 1 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  164 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 176 2 1 82 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 176 (accept_3_2 1
  164 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 176))))))))))))) (allB_succ' 14 163 176 (Eq.refl
  Bool.true) (allA_of_3_0 14 163 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 162 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 162 176 2 7 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 162 176 (accept_3_2 13 162 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  162 176 2 6 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 162 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 162 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 162 176 2 5 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 162 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 176 2 4 81 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 176 (accept_3_2 7 162 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 176 2 3 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 176 (Polychromatic418967fa.accept_21_5_15_8_1_9935 5 162 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 176 2 2 81 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 162 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 162 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 162 176 2 1 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 162 176 (accept_3_2 1 162 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  176))))))))))))))) (allB_succ' 16 161 176 (Eq.refl Bool.true) (allA_succ_of_accept 15 161 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 161 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 161 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 176 (accept_3_2 13 161 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 161 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 176 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 176 (accept_3_2 10
  161 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 161 176 (Polychromatic418967fa.accept_27_8_26_14_1_9953 8 161 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 176 (accept_3_2 7 161 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 161 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 5
  161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 176 (accept_3_2 4 161
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 176 (accept_3_2 1 161 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  176)))))))))))))))) (allB_succ' 17 160 176 (Eq.refl Bool.true) (allA_of_3_0 17 160 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 159 176 (Eq.refl Bool.true) (allA_succ_of_accept 17 159 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 176 (accept_3_2 16 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 176 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 159 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 176 (accept_3_2 13 159 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 176 (accept_3_2 10 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 159 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 176 (accept_3_2 7 159 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 176 (accept_3_2 4 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 159 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 176 (accept_3_2 1 159 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 176)))))))))))))))))) (allB_succ' 19 158 176 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 158 176 2 9 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 158 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 176 2 8 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 176 (Polychromatic418967fa.accept_19_15_6_5_1_4356
  15 158 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 176 2 7 79 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 176
  (accept_3_2 13 158 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 176 2 6 79 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 158 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 176 2 5 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 176 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 158 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 176 2 4 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 176 (accept_3_2 7 158 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 176 2 3 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 158 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 176 2 2 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  158 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 176 2 1 79 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 176 (accept_3_2 1
  158 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 176))))))))))))))))))) (allB_succ' 20 157 176 (Eq.refl
  Bool.true) (allA_of_3_0 20 157 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 156 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 156 176 4 5 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 176 (accept_3_2 19 156 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  156 176 2 9 78 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 156 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 156 176 4 4 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 156 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 156 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 176 2 7 78 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 176 (accept_3_2 13 156 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 176 4 3 39 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 156 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 176 2 5 78 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 156 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 176 4 2 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 176 (accept_3_2 7 156 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 156 176 2 3 78 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 156 176 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 156 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 176 4 1 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  156 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 176 2 1 78 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 176 (accept_3_2 1
  156 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 176))))))))))))))))))))) (allB_succ' 22 155 176
  (Eq.refl Bool.true) (allA_succ_of_accept 21 155 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 176
  (Polychromatic418967fa.accept_18_2_11_14_1_69 20 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 176 (accept_3_2 19 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 176 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 155 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 176 (accept_3_2 16 155 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 176 (accept_3_2 13 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 176 (accept_3_2 10 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 176 (accept_3_2 7 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 176 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 176 (accept_3_2 4 155 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 176 (accept_3_2 1 155 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  176)))))))))))))))))))))) (allB_succ' 23 154 176 (Eq.refl Bool.true) (allA_of_3_0 23 154 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 153 176 (Eq.refl Bool.true) (allA_succ_of_accept 23 153 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 176 (accept_3_2 22 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 176 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 176 (Polychromatic418967fa.accept_24_20_9_8_1_9926 20 153 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 176 (accept_3_2 19 153 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 153
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 176 (accept_3_2 16 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 176 (Polychromatic418967fa.accept_19_15_1_5_1_3013 15 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 176 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 153 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 176 (accept_3_2 13 153 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 176 (accept_3_2 10 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 153 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 176 (accept_3_2 7 153 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 176 (accept_3_2 4 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 176 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 153 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 153 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 176 (accept_3_2 1 153 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 176)))))))))))))))))))))))) (allB_succ' 25 152 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 152 176 8 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 152 176 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 152 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 176 2 11 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  152 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 176 4 5 38 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 176 (accept_3_2 19
  152 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 176 2 9 76 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 176 8 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 152 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 176 2 7 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 176 (accept_3_2 13 152 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 176 4 3 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 176 2 5 76 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 176
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 152 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 176 8 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 176 (accept_3_2 7 152 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  176 2 3 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 152 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 176 4 1 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 176 2 1 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 176 (accept_3_2 1 152 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 176))))))))))))))))))))))))) (allB_succ' 26 151 176 (Eq.refl Bool.true)
  (allA_of_3_0 26 151 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 150 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 150 176 2 13 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 176 (accept_3_2 25 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 176 2 12 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 176 2 11 75 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 176 2 10 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 176 (accept_3_2 19 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 176 2 9 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 176 2 8 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 176 (Polychromatic418967fa.accept_12_3_6_8_1_969
  15 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 176 2 7 75 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 176
  (accept_3_2 13 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 176 2 6 75 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 176 2 5 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 150 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 176 2 4 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 176 (accept_3_2 7 150 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 150 176 2 3 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 150 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 150 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 176 2 2 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3
  150 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 176 2 1 75 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 176 (accept_3_2 1
  150 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 176))))))))))))))))))))))))))) (allB_succ' 28 149 176
  (Eq.refl Bool.true) (allA_succ_of_accept 27 149 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 176 (accept_3_2 25 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 176 (accept_3_2 22 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 176 (accept_3_2 19 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 176 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 176 (accept_3_2 16 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 176 (accept_3_2 13 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 176 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 176 (Polychromatic418967fa.accept_17_11_13_6_1_2625 11 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 176 (accept_3_2 10 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 176
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 8 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 176 (accept_3_2 7 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 176 (accept_3_2 4 149 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 176 (accept_3_2 1 149 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  176)))))))))))))))))))))))))))) (allB_succ' 29 148 176 (Eq.refl Bool.true) (allA_of_3_0 29 148 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 147 176 (Eq.refl Bool.true) (allA_succ_of_accept 29 147 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 176 (accept_3_2 28 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 176 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 176 (accept_3_2 25 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 176 (accept_3_2 22 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 176 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 176 (accept_3_2 19 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 176 (accept_3_2 16 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 176 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 147 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 176 (accept_3_2 13 147 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 176 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 147
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 176 (accept_3_2 10 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 176 (accept_3_2 7 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 176 (accept_3_2 4 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 176 (accept_3_2 1 147 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 176)))))))))))))))))))))))))))))) (allB_succ' 31 146 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 146 176 2 15 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 146 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 176 2 14 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 176
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 146 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 176 2 13 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 176 (accept_3_2 25 146 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 176 2 12 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 146 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 176 2 11 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 146 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 176 2 10 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 176 (accept_3_2 19 146 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 176 2 9 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 146 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 176 2 8 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  146 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 176 2 7 73 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 176 (accept_3_2 13
  146 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 176 2 6 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 146 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 176 2 5 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 146 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 176 2 4 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 176 (accept_3_2 7 146 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 176 2 3 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 176 2 2 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  146 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 176 2 1 73 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 176 (accept_3_2 1
  146 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 176))))))))))))))))))))))))))))))) (allB_succ' 32 145
  176 (Eq.refl Bool.true) (allA_of_3_0 32 145 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 144 176
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 176 16 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 144 176 (accept_3_2 31 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 176 2 15 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 176 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 144 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 176 4 7 36 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 176
  (Polychromatic418967fa.accept_28_27_4_8_1_9952 27 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 176 2 13 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 176 (accept_3_2 25 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 176 8 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 176 (Polychromatic418967fa.accept_27_23_9_14_1_9951 23 144 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 176 2 11 72 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 176
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 176 4 5 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 176 (accept_3_2 19 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  144 176 2 9 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 144 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 176 16 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 144 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 144 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 176 2 7 72 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 176 (accept_3_2 13 144 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 176 4 3 36 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 176
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 144 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 176 2 5 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 176 (Polychromatic418967fa.accept_17_9_8_6_1_6050 9 144 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 176 8 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 176 (accept_3_2 7 144 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 176 2 3 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 144 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 176 4 1 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  144 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 176 2 1 72 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 176 (accept_3_2 1
  144 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 176))))))))))))))))))))))))))))))))) (allB_succ' 34 143
  176 (Eq.refl Bool.true) (allA_succ_of_gcd 33 143 176 11 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 143 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 176 (accept_3_2 31 143 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 176 (accept_3_2 28 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 176 (accept_3_2 25 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 143 176 11 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 143 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 176 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 176 (accept_3_2 19
  143 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 143 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 176 (accept_3_2 16 143 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 143 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 176 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 176 (accept_3_2 13
  143 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 143 176 11 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 143 176 (accept_3_2 10 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 143 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 176 (accept_3_2 7 143 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 176 (accept_3_2 4 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 176 (accept_3_2 1 143 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 176)))))))))))))))))))))))))))))))))) (allB_succ' 35 142 176 (Eq.refl Bool.true)
  (allA_of_3_0 35 142 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 141 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 176 (accept_3_2 34 141 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 176 (accept_3_2 31 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 176 (accept_3_2 28 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 176 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 176 (accept_3_2 25 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 176 (accept_3_2 22 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 176 (accept_3_2 19 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 176 (accept_3_2 16 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 176
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 176 (accept_3_2 13 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 176 (accept_3_2 10 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 176 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 176 (accept_3_2 7 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 176 (accept_3_2 4 141 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 141 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 176 (accept_3_2 1 141 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  176)))))))))))))))))))))))))))))))))))) (allB_succ' 37 140 176 (Eq.refl Bool.true) (allA_succ_of_gcd 36 140 176 4 9 35
  44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 140 176
  (Polychromatic418967fa.accept_25_10_15_1_1_9950 35 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 140 176 2 17 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 140 176 (Polychromatic418967fa.accept_21_12_14_8_1_5258 33 140 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 176 4 8 35 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 176 (accept_3_2 31
  140 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 176 2 15 70 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 176
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 176 4 7 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 176 (Polychromatic418967fa.accept_17_10_4_6_1_3757 27 140 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 176 2 13 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 176 (accept_3_2 25 140 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 176 4 6 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 176 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 140
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 176 2 11 70 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 176
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 176 4 5 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 176 (accept_3_2 19 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 176 2 9 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 140 176 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 140 176 4 4 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 140 176 (Polychromatic418967fa.accept_21_15_14_8_1_6826 15 140 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 176 2 7 70 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 176 (accept_3_2 13
  140 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 176 4 3 35 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 176
  (Polychromatic418967fa.accept_17_11_4_6_1_2631 11 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 176 2 5 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 176 (Polychromatic418967fa.accept_15_9_5_11_1_5416 9 140 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 176 4 2 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 176 (accept_3_2 7 140 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 176 2 3 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 176 (Polychromatic418967fa.accept_17_5_4_6_1_7342 5 140 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 176 4 1 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 176 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  3 140 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 176 2 1 70 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 176 (accept_3_2 1
  140 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 176))))))))))))))))))))))))))))))))))))) (allB_succ' 38
  139 176 (Eq.refl Bool.true) (allA_of_3_0 38 139 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 138 176
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 176 2 19 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 176 (accept_3_2 37 138 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 138 176 2 18 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 138 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 176 2 17 69 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 176 2 16 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 176 (accept_3_2 31 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 176 2 15 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 138 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 176 2 14 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 176 2 13 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 176 (accept_3_2 25 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 176 2 12 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 138 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 176 2 11 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 176 2 10 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 176 (accept_3_2 19 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 176 2 9 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 176 2 8 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 176 2 7 69 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 176 (accept_3_2 13
  138 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 176 2 6 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 176 2 5 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 176 2 4 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 176 (accept_3_2 7 138 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 176 2 3 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 176 (Polychromatic418967fa.accept_20_5_18_16_1_1558 5 138 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 176 2 2 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 138 176 2 1 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 176 (accept_3_2 1 138 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  176))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 137 176 (Eq.refl Bool.true) (allA_succ_of_accept 39 137 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 137 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 176 (accept_3_2 37 137 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 137 176 (Polychromatic418967fa.accept_15_6_2_11_1_325 36 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 176 (accept_3_2 34 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 176 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 176 (accept_3_2 31 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 137 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 176
  (Polychromatic418967fa.accept_17_12_1_6_1_3680 29 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 176 (accept_3_2 28 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 176 (accept_3_2 25 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 176
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 176 (accept_3_2 22 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 176 (accept_3_2 19 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 176 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 137
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 176 (accept_3_2 16 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 176 (accept_3_2 13 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 176
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 176 (accept_3_2 10 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 176 (accept_3_2 7 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 137 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 176 (accept_3_2 4 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 176 (accept_3_2 1 137 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 176)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 136 176 (Eq.refl
  Bool.true) (allA_of_3_0 41 136 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 135 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 176 (accept_3_2 40 135 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 176 (accept_3_2 37 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 176 (Polychromatic418967fa.accept_19_17_2_5_1_7085 36 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 176 (accept_3_2 34 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 176 (Polychromatic418967fa.accept_19_14_2_5_1_9949 33 135 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 176
  (Polychromatic418967fa.accept_25_7_10_1_1_9948 32 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 176 (accept_3_2 31 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 176 (accept_3_2 28 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 176
  (Polychromatic418967fa.accept_17_9_16_6_1_4820 26 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 176 (accept_3_2 25 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 176 (accept_3_2 22 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 176 (accept_3_2 19 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 176 (accept_3_2 16 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 176 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 176 (accept_3_2 13 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 176 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 176 (accept_3_2 10 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 176
  (Polychromatic418967fa.accept_19_8_2_5_1_5678 8 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 176 (accept_3_2 7 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 176 (accept_3_2 4 135 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 176
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 176 (accept_3_2 1 135 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  176)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 134 176 (Eq.refl Bool.true) (allA_succ_of_gcd 42 134 176
  2 21 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 134
  176 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 134 176 2 20 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 134 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 134 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 134 176 2 19 67 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 134 176 (accept_3_2 37 134 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 134 176 2 18 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 176
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 134 176 2 17 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 134 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 134 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 134 176 2 16 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 134 176 (accept_3_2 31 134 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 134 176 2 15 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 134 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 176 2 14 67 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 176
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 134 176 2 13 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 134 176 (accept_3_2 25 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 176 2 12 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 134 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 176 2 11 67 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 176 2 10 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 176 (accept_3_2 19 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 176 2 9 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 134 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 176 2 8 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 176 2 7 67 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 176 (accept_3_2 13
  134 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 176 2 6 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 176 2 5 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 134 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 176 2 4 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 176 (accept_3_2 7 134 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 176 2 3 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 134 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 176 2 2 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  134 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 176 2 1 67 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 176 (accept_3_2 1
  134 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 176)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 133 176 (Eq.refl Bool.true) (allA_of_3_0 44 133 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 132 176 (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 176 44 1 3 4 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 176 (accept_3_2 43 132 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 176 2 21 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 176 (Polychromatic418967fa.accept_10_1_2_6_1_638
  41 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 176 4 10 33 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 176 2 19 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 176 (accept_3_2 37 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 176 4 9 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 176 2 17 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 176 11 3 12 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 176 4 8 33 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 176 (accept_3_2 31 132 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 176 2 15 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 29
  132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 176 4 7 33 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 176
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 176 2 13 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 176 (accept_3_2 25 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 176 4 6 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 176 22 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 176 4 5 33 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 176 (accept_3_2 19
  132 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 176 2 9 66 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 176 4 4 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 132 176 (Polychromatic418967fa.accept_21_15_6_8_1_9888 15 132 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 176 2 7 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 176 (accept_3_2 13 132 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 176 4 3 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 176 11 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 176 2 5 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 176 4 2 33 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 176 (accept_3_2 7
  132 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 176 2 3 66 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 176 4 1 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 132 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 176 2 1 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 176 (accept_3_2 1 132 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 176))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 131 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 176 (Polychromatic418967fa.accept_17_10_12_6_1_4917 44 131
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 176 (accept_3_2 43 131
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 131 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 176 (accept_3_2 40 131 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 176 (accept_3_2 37
  131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 176
  (Polychromatic418967fa.accept_17_2_12_6_1_3737 36 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 131 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 131 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 176 (accept_3_2 34 131 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 176 (Polychromatic418967fa.accept_7_4_5_1_1_418
  32 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 176 (accept_3_2 31
  131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 176
  (Polychromatic418967fa.accept_19_11_17_5_1_8609 30 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 176 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 176 (accept_3_2 28 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 176 (accept_3_2 25 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 176 (Polychromatic418967fa.accept_21_2_5_8_1_433 23 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 176 (accept_3_2 22 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 176 (accept_3_2 19 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 176 (accept_3_2 16 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 176 (accept_3_2 13 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 176 (accept_3_2 10 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 176
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 176 (accept_3_2 7 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 176 (accept_3_2 4 131 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 176 (accept_3_2 1 131 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  176)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 130 176 (Eq.refl Bool.true) (allA_of_3_0 47 130 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 129 176 (Eq.refl Bool.true) (allA_succ_of_accept 47 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 176 (accept_3_2 46 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 176 (accept_3_2 43 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 176 (accept_3_2 40 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 176 (accept_3_2 37 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 176 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 129 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 176 (accept_3_2 34 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 176 (accept_3_2 31 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 176 (accept_3_2 28 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 176 (accept_3_2 25 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 176 (accept_3_2 22 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 176 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 176 (accept_3_2 19 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 176 (accept_3_2 16 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 176 (Polychromatic418967fa.accept_21_14_3_8_1_3806 14 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 176 (accept_3_2 13 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 176 (accept_3_2 10 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 176 (accept_3_2 7 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 129 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 176 (accept_3_2 4 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 129 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 176 (accept_3_2 1 129 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 176)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 128 176 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 128 176 16 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 176 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 128 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 176 2 23 64 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 176 4 11 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 176 (accept_3_2 43 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 176 2 21 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 176 8 5 16 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 176 2 19 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 176 (accept_3_2 37 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 176 4 9 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 176 2 17 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 176 16 2 8 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 176 (accept_3_2 31
  128 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 176 2 15 64 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 176
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 176 4 7 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 176 2 13 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 176 (accept_3_2 25 128 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 176 8 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 128 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 176 2 11 64 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 176 4 5 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 176 (accept_3_2 19 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 176 2 9 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 128 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 128 176 16 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 128 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 176 2 7 64 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 176 (accept_3_2 13 128 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 176 4 3 32 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 176
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 176 2 5 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 176 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 128 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 176 8 1 16 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 176 (accept_3_2 7 128 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 176 2 3 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 176 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 128 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 176 4 1 32 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 176 2 1 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 176 (accept_3_2 1 128 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  176))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 127 176 (Eq.refl Bool.true) (allA_of_3_0 50 127
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 126 176 (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 176 2
  25 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126
  176 (accept_3_2 49 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 176 2 24 63 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 176
  (Polychromatic418967fa.accept_13_8_9_7_1_530 47 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 176 2 23 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 176 2 22 63 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 176 (accept_3_2 43 126 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 176 2 21 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 176 (Polychromatic418967fa.accept_13_2_9_7_1_164
  41 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 176 2 20 63 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 176 2 19 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 176 (accept_3_2 37 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 176 2 18 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 176 (Polychromatic418967fa.accept_15_5_6_11_1_854 35 126 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 176 2 17 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 176 2 16 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 176 (accept_3_2 31 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 176 2 15 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 176 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 126 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 176 2 14 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 176 2 13 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 176 (accept_3_2 25 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 176 2 12 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 176 (Polychromatic418967fa.accept_19_4_12_5_1_8615 23 126 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 176 2 11 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 176 2 10 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 176 (accept_3_2 19 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 176 2 9 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 176 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 126 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 176 2 8 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 176 (Polychromatic418967fa.accept_12_3_6_8_1_969
  15 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 176 2 7 63 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 176
  (accept_3_2 13 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 176 2 6 63 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 176
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 176 2 5 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 176 2 4 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 176 (accept_3_2 7 126 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 126 176 2 3 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 176 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 126 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 176 2 2 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  126 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 176 2 1 63 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 176 (accept_3_2 1
  126 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 176)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 125 176 (Eq.refl Bool.true) (allA_succ_of_accept 51 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 176 (accept_3_2 49 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 176 (accept_3_2 46 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 176 (accept_3_2 43 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 176 (accept_3_2 40 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 176 (accept_3_2 37 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 176 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 176 (accept_3_2 34 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 176
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 176 (accept_3_2 31 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 176 (accept_3_2 28 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 176 (accept_3_2 25 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 176 (accept_3_2 22 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 176 (accept_3_2 19 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 176 (Polychromatic418967fa.accept_20_18_5_16_1_5425 18 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 176 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 176 (accept_3_2 16 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 176 (accept_3_2 13 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 176 (accept_3_2 10 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 176
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 176 (accept_3_2 7 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 176 (accept_3_2 4 125 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 176 (accept_3_2 1 125 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  176)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 124 176 (Eq.refl Bool.true) (allA_of_3_0 53 124
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 123 176 (Eq.refl Bool.true) (allA_succ_of_accept 53 123
  176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 176 (accept_3_2 52 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 176 (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 176 (Polychromatic418967fa.accept_19_12_9_5_1_8593 50 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 176 (accept_3_2 49 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 123 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 176 (accept_3_2 46 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 176 (accept_3_2 43 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 176 (accept_3_2 40 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 176 (accept_3_2 37 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 176 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 176 (accept_3_2 34 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 176 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 176 (accept_3_2 31 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 123 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 176 (accept_3_2 28 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 176 (accept_3_2 25 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 176 (accept_3_2 22 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 176 (accept_3_2 19 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 176 (accept_3_2 16 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 176 (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 176 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 176 (accept_3_2 13 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 176 (accept_3_2 10 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 176 (accept_3_2 7 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 123 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 176 (accept_3_2 4 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 176 (accept_3_2 1 123 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 176)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 122 176
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 122 176 2 27 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 122 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 122 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 176 2 26 61 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 176 2 25 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 176 (accept_3_2 49 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 176 2 24 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 122 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 176 2 23 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 176
  (Polychromatic418967fa.accept_21_3_17_8_1_8402 45 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 176 2 22 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 176 (accept_3_2 43 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 176 2 21 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 122 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 176 2 20 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 176 2 19 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 176 (accept_3_2 37 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 176 2 18 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 122 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 176 2 17 61 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 176 2 16 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 176 (accept_3_2 31 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 176 2 15 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 122 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 176 2 14 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 176
  (Polychromatic418967fa.accept_24_3_2_8_1_4572 27 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 176 2 13 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 176 (accept_3_2 25 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 176 2 12 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 176 2 11 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 176 2 10 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 176 (accept_3_2 19 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 176 2 9 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 176 2 8 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 176 (Polychromatic418967fa.accept_13_2_5_7_1_1695
  15 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 176 2 7 61 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 176
  (accept_3_2 13 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 176 2 6 61 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 176 2 5 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 176 2 4 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 176 (accept_3_2 7 122 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 176 2 3 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 176 2 2 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 176 (Polychromatic418967fa.accept_19_3_8_5_1_1875 3
  122 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 176 2 1 61 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 176 (accept_3_2 1
  122 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 121 176 (Eq.refl Bool.true) (allA_of_3_0 56
  121 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 120 176 (Eq.refl Bool.true) (allA_succ_of_gcd 56 120
  176 8 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  120 176 (accept_3_2 55 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 120 176 2 27 60 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 176 4 13 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 176 2 25 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 176 (accept_3_2 49 120 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 176 8 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 47
  120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 176 2 23 60 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 176
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 45 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 176 4 11 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 176 (accept_3_2 43 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 176 2 21 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 176 (Polychromatic418967fa.accept_19_3_6_5_1_9947 41 120 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 176 8 5 15 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 176
  (Polychromatic418967fa.accept_17_5_1_6_1_2615 39 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 176 2 19 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 176 (accept_3_2 37 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 176 4 9 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 176 2 17 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 176 8 4 15 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 176 (accept_3_2 31
  120 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 176 2 15 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 176 4 7 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 176 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 120 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 176 2 13 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 176 (accept_3_2 25 120 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 176 8 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 176 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 120
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 176 2 11 60 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 176
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 176 4 5 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 176 (accept_3_2 19 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 176 2 9 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 120 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 176 8 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 120 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 176 2 7 60 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 176 (accept_3_2 13 120 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 176 4 3 30 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 176 2 5 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 120 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 120 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 176 8 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 176 (accept_3_2 7 120 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 120 176 2 3 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 120 176 (Polychromatic418967fa.accept_17_5_1_6_1_2615 5 120 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 176 4 1 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 176 (Polychromatic418967fa.accept_17_3_1_6_1_251 3
  120 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 176 2 1 60 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 176 (accept_3_2 1
  120 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 119 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 176 (Polychromatic418967fa.accept_18_2_11_14_1_69 56 119
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 176 (accept_3_2 55 119
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 176
  (Polychromatic418967fa.accept_21_12_14_8_1_5258 54 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 176 (accept_3_2 52 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 176 (accept_3_2 49 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 176 (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 176 (accept_3_2 46 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 176 (accept_3_2 43 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 176 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 176 (accept_3_2 40 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 176 (accept_3_2 37 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 176 (Polychromatic418967fa.accept_21_15_14_8_1_6826 36 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 176 (accept_3_2 34 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 176
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 32 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 119 176 (accept_3_2 31 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 119 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 176 (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 119
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 176 (accept_3_2 28 119
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 176 (accept_3_2 25 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 176 (Polychromatic418967fa.accept_10_3_9_6_1_94
  23 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 176 (accept_3_2 22
  119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 119 176 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 176 (accept_3_2 19 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 119 176 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 176 (accept_3_2 16 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 176 (accept_3_2 13 119 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 176
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 176 (accept_3_2 10 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 176 (accept_3_2 7 119 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 176
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 176 (accept_3_2 4 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 176 (accept_3_2 1 119 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 118
  176 (Eq.refl Bool.true) (allA_of_3_0 59 118 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 117 176
  (Eq.refl Bool.true) (allA_succ_of_accept 59 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 176 (accept_3_2 58 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 176 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 117
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 176
  (Polychromatic418967fa.accept_21_14_12_8_1_6833 56 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 117 176 (accept_3_2 55 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 117 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 176 (accept_3_2 52 117 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 176 (Polychromatic418967fa.accept_10_1_7_6_1_91
  51 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 176
  (Polychromatic418967fa.accept_23_4_2_15_1_9946 50 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 176 (accept_3_2 49 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 176 (accept_3_2 46 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 176
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 117 176 (accept_3_2 43 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 117 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 176 (accept_3_2 40 117 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 176 (Polychromatic418967fa.accept_7_4_5_1_1_418
  39 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 176 (accept_3_2 37 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 176 (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 176 (accept_3_2 34 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 176 (accept_3_2 31 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 176 (accept_3_2 28 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 176
  (Polychromatic418967fa.accept_17_9_15_6_1_3744 26 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 176 (accept_3_2 25 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 176 (accept_3_2 22 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 176 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 176 (accept_3_2 19 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 176 (accept_3_2 16 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 176 (Polychromatic418967fa.accept_21_15_12_8_1_5275 15 117 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 176
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 176 (accept_3_2 13 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 117 176 (Polychromatic418967fa.accept_25_12_17_1_1_9945 12 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 176 (accept_3_2 10
  117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 176
  (Polychromatic418967fa.accept_17_9_15_6_1_3744 9 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 176 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 117 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 176 (accept_3_2 7 117 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5
  117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 176 (accept_3_2 4 117
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 176 (Polychromatic418967fa.accept_7_3_5_1_1_72
  3 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 176
  (Polychromatic418967fa.accept_19_2_3_5_1_5721 2 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 176 (accept_3_2 1 117 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 116 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 116 176 4 15 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 116 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 176 2 29 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 176 4 14 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 176 (accept_3_2 55 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 176 2 27 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 176 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 116 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 176 4 13 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 176
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 176 2 25 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 176 (accept_3_2 49 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 176 4 12 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 116 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 176 2 23 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 176 4 11 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 176 (accept_3_2 43 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 176 2 21 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 176 (Polychromatic418967fa.accept_17_7_14_6_1_4882 41 116 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 176 4 10 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 176 2 19 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 176 (accept_3_2 37 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 176 4 9 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 176 (Polychromatic418967fa.accept_19_16_2_5_1_5681 35 116 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 176 2 17 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 176 4 8 29 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 176 (accept_3_2 31
  116 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 176 2 15 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 176 4 7 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 176 (Polychromatic418967fa.accept_19_8_2_5_1_5678 27 116 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 176 2 13 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 176 (accept_3_2 25 116 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 176 4 6 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 176 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 116
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 176 2 11 58 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 176 4 5 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 176 (accept_3_2 19 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 176 2 9 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 176 4 4 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 116 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 176 2 7 58 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 176 (accept_3_2 13 116 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 176 4 3 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 176 2 5 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 176 (Polychromatic418967fa.accept_23_9_1_15_1_6470 9 116 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 176 4 2 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 176 (accept_3_2 7 116 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 176 2 3 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 176 4 1 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  116 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 176 2 1 58 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 176 (accept_3_2 1
  116 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 115 176 (Eq.refl Bool.true)
  (allA_of_3_0 62 115 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 114 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 114 176 2 31 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 176 (accept_3_2 61 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 176 2 30 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 176 2 29 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 176 2 28 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 176 (accept_3_2 55 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 176 2 27 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 176 2 26 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 176 2 25 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 176 (accept_3_2 49 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 176 2 24 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 176 2 23 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 176 2 22 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 176 (accept_3_2 43 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 176 2 21 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 176 2 20 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 176 2 19 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 176 (accept_3_2 37 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 176 2 18 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 176 2 17 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 176 2 16 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 176 (accept_3_2 31 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 176 2 15 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 176 2 14 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 176 2 13 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 176 (accept_3_2 25 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 176 2 12 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 176 (Polychromatic418967fa.accept_24_23_18_8_1_4564 23 114 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 176 2 11 57 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 176 2 10 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 176 (accept_3_2 19 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 176 2 9 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 176 2 8 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 176 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 176 2 7 57 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 176
  (accept_3_2 13 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 176 2 6 57 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 176 2 5 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 176 2 4 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 176 (accept_3_2 7 114 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 176 2 3 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 114 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 176 2 2 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  114 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 176 2 1 57 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 176 (accept_3_2 1
  114 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 113 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 113
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 176 (accept_3_2 61 113
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 176
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 113 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 59 113 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 176 (accept_3_2 58 113 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 176 (Polychromatic418967fa.accept_13_4_9_7_1_2402
  56 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 176 (accept_3_2 55
  113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 176
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 113 176 (Polychromatic418967fa.accept_23_7_21_15_1_9930 53 113 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 176 (accept_3_2 52 113 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 176 (accept_3_2 49 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 176 (accept_3_2 46 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 176
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 176 (accept_3_2 43 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 176 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 176 (Polychromatic418967fa.accept_13_2_9_7_1_164 41 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 176 (accept_3_2 40 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 176 (accept_3_2 37 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 176 (Polychromatic418967fa.accept_19_17_18_5_1_3012 36 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 176 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 176 (accept_3_2 34 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 176
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 176 (accept_3_2 31 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 176 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 29 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 176 (accept_3_2 28 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 176 (accept_3_2 25 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 176 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 176 (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 176 (accept_3_2 22 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 176
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 176 (accept_3_2 19 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 176 (accept_3_2 16 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 176 (accept_3_2 13 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 176 (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 176 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 176 (accept_3_2 10 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 176 (accept_3_2 7 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 176 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 176 (accept_3_2 4 113 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 176 (accept_3_2 1 113 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 112 176 (Eq.refl Bool.true)
  (allA_of_3_0 65 112 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 111 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 176 (accept_3_2 64 111 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 176 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 176 (accept_3_2 61 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 176 (accept_3_2 58 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 176 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 176 (accept_3_2 55 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 176 (accept_3_2 52 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 176
  (Polychromatic418967fa.accept_15_5_6_11_1_854 50 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 176 (accept_3_2 49 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 176 (accept_3_2 46 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 176 (accept_3_2 43 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 176 (accept_3_2 40 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 111 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 176 (accept_3_2 37 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 176 (Polychromatic418967fa.accept_21_15_6_8_1_9888 36 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 176 (accept_3_2 34 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 176 (accept_3_2 31 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 176 (accept_3_2 28 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 176 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 176 (accept_3_2 25 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 176 (accept_3_2 22 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 176 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 111 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 176 (accept_3_2 19 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 176 (accept_3_2 16 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 176
  (Polychromatic418967fa.accept_19_14_16_5_1_5668 14 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 111 176 (accept_3_2 13 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 176 (accept_3_2 10 111 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 176 (accept_3_2 7 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 176 (accept_3_2 4 111 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 111 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 176 (accept_3_2 1 111 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 110 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 110 176 22 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 110 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 176 2 32 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 176 (Polychromatic418967fa.accept_19_6_15_5_1_5697
  63 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 110 176 2 31 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 110 176
  (accept_3_2 61 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 110 176 2 30 55 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 110 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 110 176 2 29 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 110 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 110 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 110 176 2 28 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 110 176 11 5 10 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 176 2 27 55 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 110 176 2 26 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 110 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 110 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 176 2 25 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 176 (accept_3_2 49 110 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 110 176 2 24 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 110 176 (Polychromatic418967fa.accept_12_11_2_8_1_511
  47 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 176 2 23 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 176 22 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 110 176 (accept_3_2 43 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  110 176 2 21 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 110 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 176 2 20 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 39
  110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 176 2 19 55 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 176 (accept_3_2 37
  110 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 176 2 18 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 110 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 110 176 2 17 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 110 176 11 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 110 176 2 16 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 110 176 (accept_3_2 31 110 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 110 176 2 15 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 110 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 176 2 14 55 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 176 2 13 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 176 (accept_3_2 25 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 176 2 12 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 110 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 176 22 1 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 176 2 10 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 176 (accept_3_2 19 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 176 2 9 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 176 2 8 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 176 2 7 55 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 176 (accept_3_2 13
  110 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 176 2 6 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 110 176 11 1 10 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 110 176 2 5 55 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 176
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 176 2 4 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 176 (accept_3_2 7 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  176 2 3 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 176 2 2 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 110 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 176 2 1 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 176 (accept_3_2 1 110 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 109 176 (Eq.refl Bool.true) (allA_of_3_0 68 109 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 108 176
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 176 4 17 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 176 (accept_3_2 67 108 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 108 176 2 33 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 108 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 176 4 16 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 176
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 176 2 31 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 176 (accept_3_2 61 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 176 4 15 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 176 (Polychromatic418967fa.accept_15_14_3_11_1_850 59 108 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 176 2 29 54 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 176
  (Polychromatic418967fa.accept_21_15_3_8_1_6822 57 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 176 4 14 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 176 (accept_3_2 55 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 176 2 27 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 176 4 13 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 176 2 25 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 176 (accept_3_2 49 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 176 4 12 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 176 2 23 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 176
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 176 4 11 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 176 (accept_3_2 43 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 176 2 21 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 176 (Polychromatic418967fa.accept_24_17_12_8_1_2990 41 108 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 176 4 10 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 176 2 19 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 176 (accept_3_2 37 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 176 4 9 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 108 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 176 2 17 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 176 4 8 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 176 (accept_3_2 31
  108 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 176 2 15 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 176
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 176 4 7 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 176 (Polychromatic418967fa.accept_19_8_13_5_1_1889 27 108 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 176 2 13 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 176 (accept_3_2 25 108 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 176 4 6 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 176 2 11 54 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 176
  (Polychromatic418967fa.accept_15_6_3_11_1_848 21 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 176 4 5 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 176 (accept_3_2 19 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 176 2 9 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 108 176 (Polychromatic418967fa.accept_21_17_3_8_1_6793 17 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 176 4 4 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 108 176 (Polychromatic418967fa.accept_21_15_3_8_1_6822 15 108 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 176 2 7 54 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 176 (accept_3_2 13 108 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 176 4 3 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 176 2 5 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 176 4 2 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 176 (accept_3_2 7 108 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 108 176 2 3 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 108 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 176 4 1 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 3
  108 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 176 2 1 54 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 176 (accept_3_2 1
  108 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 107 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 176 (Polychromatic418967fa.accept_19_11_12_5_1_7124 68 107
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 176 (accept_3_2 67 107
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 107 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 176 (accept_3_2 64 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 176 (Polychromatic418967fa.accept_7_6_2_1_1_214
  62 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 176 (accept_3_2 61
  107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 176
  (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 107 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 176 (accept_3_2 58 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 176 (Polychromatic418967fa.accept_9_2_8_5_1_228
  56 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 176 (accept_3_2 55
  107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 176
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 107 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 53 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 176 (accept_3_2 52 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 176 (Polychromatic418967fa.accept_12_2_11_8_1_504
  50 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 176 (accept_3_2 49
  107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 107 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 176 (accept_3_2 46 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 176
  (Polychromatic418967fa.accept_25_19_7_1_1_9944 44 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 176 (accept_3_2 43 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 176 (accept_3_2 40 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 176 (accept_3_2 37 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 176 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 176 (accept_3_2 34 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 176
  (Polychromatic418967fa.accept_19_13_12_5_1_9943 32 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 107 176 (accept_3_2 31 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 107 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 176 (accept_3_2 28 107 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 176 (accept_3_2 25 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 176 (accept_3_2 22 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 176 (accept_3_2 19 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 176 (Polychromatic418967fa.accept_17_1_5_6_1_3717 18 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 176 (accept_3_2 16 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 176 (accept_3_2 13 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 176 (accept_3_2 10 107 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 176
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 176 (accept_3_2 7 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 176 (accept_3_2 4 107 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 176 (accept_3_2 1 107 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 106 176 (Eq.refl Bool.true)
  (allA_of_3_0 71 106 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 105 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 176 (accept_3_2 70 105 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 176
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 68 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 176 (accept_3_2 67 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 176 (accept_3_2 64 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 176 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 105 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 176 (accept_3_2 61 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 105 176 (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 176 (accept_3_2 58 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 176 (accept_3_2 55 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 176 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 176 (accept_3_2 52 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 176
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 50 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 176 (accept_3_2 49 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 176 (accept_3_2 46 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 176 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 176 (accept_3_2 43 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 176 (accept_3_2 40 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 176 (accept_3_2 37 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 176 (Polychromatic418967fa.accept_26_10_1_20_1_9942 36 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 176 (accept_3_2 34 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 176 (Polychromatic418967fa.accept_19_14_10_5_1_3073 33 105 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 176
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 176 (accept_3_2 31 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 176 (accept_3_2 28 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 176 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 176 (accept_3_2 25 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 176 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 176 (accept_3_2 22 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 176 (accept_3_2 19 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 176 (accept_3_2 16 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 176 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 176 (accept_3_2 13 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 176 (accept_3_2 10 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 176 (accept_3_2 7 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 176 (accept_3_2 4 105 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 176 (accept_3_2 1 105 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 104 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 104 176 8 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 176 (Polychromatic418967fa.accept_19_14_9_5_1_9941 71 104 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 176 2 35 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 176 (Polychromatic418967fa.accept_17_1_2_6_1_818
  69 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 176 4 17 26 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 176
  (accept_3_2 67 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 176 2 33 52 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 176 8 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 176 (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 104 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 176 2 31 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 176 (accept_3_2 61 104 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 176 4 15 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 176 (Polychromatic418967fa.accept_21_17_20_8_1_9938 59 104
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 176 2 29 52 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 176
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 57 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 104 176 8 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 104 176 (accept_3_2 55 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 176 2 27 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 176 (Polychromatic418967fa.accept_19_15_9_5_1_5656 53 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 176 4 13 26 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 176 2 25 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 176 (accept_3_2 49 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 176 8 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 104 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 176 2 23 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 176 (Polychromatic418967fa.accept_10_5_4_6_1_319
  45 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 176 4 11 26 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 176
  (accept_3_2 43 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 176 2 21 52 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 176
  (Polychromatic418967fa.accept_23_18_12_15_1_9940 41 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 104 176 8 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 104 176 (Polychromatic418967fa.accept_19_1_9_5_1_9939 39 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 176 2 19 52 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 176 (accept_3_2 37 104 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 176 4 9 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 176
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 176 2 17 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 104 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 176 8 4 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 176 (accept_3_2 31 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 176 2 15 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 176 (Polychromatic418967fa.accept_17_12_2_6_1_2630
  29 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 176 4 7 26 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 176
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 176 2 13 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 176 (accept_3_2 25 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 176 8 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 176 2 11 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 176 (Polychromatic418967fa.accept_14_7_6_8_1_2856
  21 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 176 4 5 26 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 176
  (accept_3_2 19 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 176 2 9 52 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 176
  (Polychromatic418967fa.accept_21_17_20_8_1_9938 17 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 104 176 8 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 176 2 7 52 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 176 (accept_3_2 13 104 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 176 4 3 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 176
  (Polychromatic418967fa.accept_21_11_20_8_1_8403 11 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 176 2 5 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 176 8 1 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 176 (accept_3_2 7 104 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 176 2 3 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 176 4 1 26 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 176
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 176 2 1 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 176 (accept_3_2 1 104 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 103 176 (Eq.refl
  Bool.true) (allA_of_3_0 74 103 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 102 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 102 176 2 37 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 176 (accept_3_2 73 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 176 2 36 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 176 2 35 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 176 2 34 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 176 (accept_3_2 67 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 176 2 33 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 176 2 32 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 176 2 31 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 176 (accept_3_2 61 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 176 2 30 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 176 2 29 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 176 2 28 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 176 (accept_3_2 55 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 176 2 27 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 176 2 26 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 176 2 25 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 176 (accept_3_2 49 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 176 2 24 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 176 2 23 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 176 2 22 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 176 (accept_3_2 43 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 176 2 21 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 176 2 20 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 176 2 19 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 176 (accept_3_2 37 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 176 2 18 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 176 2 17 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 176 2 16 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 176 (accept_3_2 31 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 176 2 15 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 176 2 14 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 176 2 13 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 176 (accept_3_2 25 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 176 2 12 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 176 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 102 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 176 2 11 51 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 176 2 10 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 176 (accept_3_2 19 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 176 2 9 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 176 2 8 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 176 2 7 51 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 176 (accept_3_2 13
  102 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 176 2 6 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 176 2 5 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 176 2 4 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 176 (accept_3_2 7 102 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 176 2 3 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 176 2 2 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  102 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 176 2 1 51 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 176 (accept_3_2 1
  102 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 101 176 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 74
  101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 176 (accept_3_2 73
  101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 101 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 101 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 176 (accept_3_2 70 101 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 176 (Polychromatic418967fa.accept_7_5_3_1_1_424
  68 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 176 (accept_3_2 67
  101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 101 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 176 (accept_3_2 64 101 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 176 (Polychromatic418967fa.accept_9_8_2_5_1_237
  62 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 176 (accept_3_2 61
  101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 101 176 (Polychromatic418967fa.accept_18_5_11_14_1_7203 59 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 176 (accept_3_2 58 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 176
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 56 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 176 (accept_3_2 55 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 176 (accept_3_2 52 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 176 (accept_3_2 49 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 176 (accept_3_2 46 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 176 (accept_3_2 43 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 176 (Polychromatic418967fa.accept_17_7_16_6_1_3705 41 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 176 (accept_3_2 40 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 176 (accept_3_2 37 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 176 (Polychromatic418967fa.accept_21_15_17_8_1_9937 36 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 176 (accept_3_2 34 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 176 (accept_3_2 31 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 176 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 176 (accept_3_2 28 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 176 (accept_3_2 25 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 176 (accept_3_2 22 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 176
  (Polychromatic418967fa.accept_18_2_11_14_1_69 20 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 176 (accept_3_2 19 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 176 (accept_3_2 16 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 176 (accept_3_2 13 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 176 (accept_3_2 10 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 176 (accept_3_2 7 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 176 (accept_3_2 4 101 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 176 (accept_3_2 1 101 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 100 176 (Eq.refl
  Bool.true) (allA_of_3_0 77 100 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 99 176 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 99 176 11 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 99 176 (accept_3_2 76 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  99 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 99 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 74 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 176 (accept_3_2 73 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 176 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 176 (accept_3_2 70 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  99 176 (Polychromatic418967fa.accept_19_12_4_5_1_9936 69 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 99 176 (Polychromatic418967fa.accept_13_3_8_7_1_4135 68 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 176 (accept_3_2 67 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 176 11 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 176 (accept_3_2 64 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 176
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 62 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 176 (accept_3_2 61 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 176 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 176 (accept_3_2 58 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 176 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 176
  (Polychromatic418967fa.accept_19_18_4_5_1_5723 56 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 99 176 11 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 99 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 99 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 176 (accept_3_2 52 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 176 (Polychromatic418967fa.accept_13_12_8_7_1_2526
  51 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 176
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 176 (accept_3_2 49 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 176 (accept_3_2 46 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 99 176 11 4 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 176 (accept_3_2 43 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 176 (accept_3_2 40 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 176 (Polychromatic418967fa.accept_18_3_9_14_1_2219 39 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 176 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 176 (accept_3_2 37 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 176 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 99
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 176 (accept_3_2 34 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99
  176 11 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  99 176 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 176 (accept_3_2 31 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 176 (accept_3_2 28 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 176 (Polychromatic418967fa.accept_13_1_8_7_1_1088
  27 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 176
  (Polychromatic418967fa.accept_21_5_15_8_1_9935 26 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 176 (accept_3_2 25 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 176 (Polychromatic418967fa.accept_17_7_14_6_1_4882 24 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 176 11 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 99 176 (Polychromatic418967fa.accept_14_7_1_8_1_2873
  21 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 176
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 176 (accept_3_2 19 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 176 (accept_3_2 16 99 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 176
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 176 (accept_3_2 13 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 176 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 99 176 11 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 99 176 (accept_3_2 10 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 99 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 99 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 176 (Polychromatic418967fa.accept_17_8_14_6_1_8727 8 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 176 (accept_3_2 7 99 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6
  99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 176 (accept_3_2 4 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  176 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 99 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 176 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 99 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 176 (accept_3_2 1 99 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  79 98 176 (Eq.refl Bool.true) (allA_succ_of_gcd 78 98 176 2 39 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 98 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 176 2 38 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 176 2 37 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 98 176 (accept_3_2 73 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 98
  176 2 36 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  98 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 98 176 2 35 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 98 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 98 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 176 2 34 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 176 (accept_3_2 67 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 176 2 33 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 98 176 2 32 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 98 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 98 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 98 176 2 31 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 176 (accept_3_2 61 98 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 176 2 30 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 176 2 29 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 176 2 28 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 98 176 (accept_3_2 55 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98
  176 2 27 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  98 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 98 176 2 26 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 98 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 176 2 25 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 176 (accept_3_2 49 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 176 2 24 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 98 176 2 23 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 98 176 (Polychromatic418967fa.accept_17_11_13_6_1_2625 45 98 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 176 2 22 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 176 (accept_3_2 43 98 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 176 2 21 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 176 2 20 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 176 2 19 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 98 176 (accept_3_2 37 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98
  176 2 18 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  98 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 98 176 2 17 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 98 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 176 2 16 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 176 (accept_3_2 31 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 176 2 15 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 176 2 14 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 176 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 98 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 176 2 13 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 176 (accept_3_2 25 98 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 176 2 12 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 98 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 176 2 11 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 176 2 10 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 98 176 (accept_3_2 19 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98
  176 2 9 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  98 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 98 176 2 8 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 98 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 98 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 176 2 7 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 176 (accept_3_2 13 98 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 176 2 6 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 98 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 176 2 5 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 176
  (Polychromatic418967fa.accept_23_9_6_15_1_9934 9 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 176 2 4 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 98 176 (accept_3_2 7 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 176
  2 3 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98
  176 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 176 2 2 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 176 2 1 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 176 (accept_3_2 1 98 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 97 176 (Eq.refl Bool.true) (allA_of_3_0 80 97 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  81 96 176 (Eq.refl Bool.true) (allA_succ_of_gcd 80 96 176 16 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 176 (accept_3_2 79 96 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 96 176 2 39 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 96 176 (Polychromatic418967fa.accept_13_12_5_7_1_1696 77 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 176 4 19 24 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 176 2 37 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 96 176 (accept_3_2 73 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96
  176 8 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  96 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 96 176 2 35 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 96 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 176 4 17 24 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 176 (accept_3_2 67 96 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 176 2 33 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 176 16 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 96 176 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 96 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 176 2 31 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 176 (accept_3_2 61 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 176 4 15 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 176 2 29 48 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 176 8 7 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 176 (accept_3_2 55 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96
  176 2 27 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  96 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 96 176 4 13 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 96 176 (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 176 2 25 48 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 176 (accept_3_2 49 96 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 176 16 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 176 2 23 48 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 176 4 11 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 176 (accept_3_2 43 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  176 2 21 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  96 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 176 8 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 176 2 19 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 176 (accept_3_2 37 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 176 4 9 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 176 2 17 48 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 176
  (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 176 16 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 176 (accept_3_2 31 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  176 2 15 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  96 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 176 4 7 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 176 2 13 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 176 (accept_3_2 25 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 176 8 3 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 176 (Polychromatic418967fa.accept_19_4_1_5_1_9933 23 96 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 176 2 11 48 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 176 4 5 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 176 (accept_3_2 19 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  176 2 9 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 176 16 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 176 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 176 2 7 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 176 (accept_3_2 13 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 176 4 3 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 96 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 176 2 5 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 176
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 176 8 1 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 176 (accept_3_2 7 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 176
  2 3 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  176 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 96 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 176 4 1 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 176 2 1 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 176 (accept_3_2 1 96 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 96 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 95 176 (Eq.refl Bool.true) (allA_succ_of_accept 81 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 81
  95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 95 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 80 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 95 176 (accept_3_2 79 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  95 176 (Polychromatic418967fa.accept_20_18_15_16_1_9893 78 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 95 176 (Polychromatic418967fa.accept_13_12_4_7_1_2520 77 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 176 (accept_3_2 76 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 95 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 74 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 95 176 (accept_3_2 73 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  95 176 (Polychromatic418967fa.accept_17_4_10_6_1_4869 72 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 95 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 71 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 176 (accept_3_2 70 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 176 (accept_3_2 67 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 95 176 (Polychromatic418967fa.accept_18_11_5_14_1_4560 65 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 176 (accept_3_2 64 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 176 (accept_3_2 61 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  95 176 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 95 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 176 (accept_3_2 58 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 176
  (Polychromatic418967fa.accept_21_14_11_8_1_5272 56 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 95 176 (accept_3_2 55 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  95 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 95 176 (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 176 (accept_3_2 52 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 176 (accept_3_2 49 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 176 (accept_3_2 46 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 176 (accept_3_2 43 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 176 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 176 (accept_3_2 40 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 176 (accept_3_2 37 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 176 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 176 (accept_3_2 34 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 176
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 176 (accept_3_2 31 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 176 (Polychromatic418967fa.accept_20_10_15_16_1_6994 30 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 176 (accept_3_2 28 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 176 (accept_3_2 25 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 176 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 176 (accept_3_2 22 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 176
  (Polychromatic418967fa.accept_21_20_11_8_1_9906 20 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 176 (accept_3_2 19 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 176 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 176 (accept_3_2 16 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 176 (accept_3_2 13 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 176 (accept_3_2 10 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 176
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 176 (accept_3_2 7 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  176 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 95 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 176 (accept_3_2 4 95 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 176 (accept_3_2 1 95 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 94 176 (Eq.refl
  Bool.true) (allA_of_3_0 83 94 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 93 176 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 176 (accept_3_2 82 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 93 176 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 80
  93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 176 (accept_3_2 79 93
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 93 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 78 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 176 (accept_3_2 76 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 93 176 (Polychromatic418967fa.accept_19_18_17_5_1_4343 75 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 176 (accept_3_2 73 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 176 (Polychromatic418967fa.accept_19_15_17_5_1_3052 72 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 176 (accept_3_2 70 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 68 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 176 (accept_3_2 67 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 176 (accept_3_2 64 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 176 (accept_3_2 61 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 176 (accept_3_2 58 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 176 (accept_3_2 55 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 176 (accept_3_2 52 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 176
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 50 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 176 (accept_3_2 49 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 176 (accept_3_2 46 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 176 (accept_3_2 43 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 176 (accept_3_2 40 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 176 (accept_3_2 37 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 176 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 176 (accept_3_2 34 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 176
  (Polychromatic418967fa.accept_17_15_8_6_1_8733 32 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 176 (accept_3_2 31 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 176 (accept_3_2 28 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 176 (accept_3_2 25 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 176 (accept_3_2 22 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 176 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 176 (accept_3_2 19 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 176 (accept_3_2 16 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 176
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 176 (accept_3_2 13 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 176 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 176 (accept_3_2 10 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 176 (accept_3_2 7 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 176 (accept_3_2 4 93 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 176 (accept_3_2 1 93 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 92 176 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 92 176 4 21 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 92 176 (Polychromatic418967fa.accept_18_11_2_14_1_3351 83 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 92 176 2 41 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 92 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 92 176 4 20 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 92 176 (accept_3_2 79 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92
  176 2 39 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  92 176 (Polychromatic418967fa.accept_19_1_16_5_1_5671 77 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 92 176 4 19 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 92 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 92 176 2 37 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 92 176 (accept_3_2 73 92 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92 176 4 18 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 92 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 92 176 2 35 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 92 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 92 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 176 4 17 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 176 (accept_3_2 67 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 176 2 33 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 92 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 92 176 4 16 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 92 176
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 92 176 2 31 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 92 176 (accept_3_2 61 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92
  176 4 15 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  92 176 (Polychromatic418967fa.accept_19_2_16_5_1_9932 59 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 92 176 2 29 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 92 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 176 4 14 23 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 176 (accept_3_2 55 92 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 176 2 27 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 92 176 4 13 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 92 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 92 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 176 2 25 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 176 (accept_3_2 49 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 176 4 12 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 176 (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 92 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 176 2 23 46 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 176
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 92 176 4 11 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 92 176 (accept_3_2 43 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92
  176 2 21 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  92 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 92 176 4 10 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 92 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 176 2 19 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 176 (accept_3_2 37 92 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 176 4 9 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 176 2 17 46 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 176
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 176 4 8 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 176 (accept_3_2 31 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  176 2 15 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 176 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 176 4 7 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 92 176 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 176 2 13 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 176 (accept_3_2 25 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 176 4 6 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 176 (Polychromatic418967fa.accept_25_23_17_1_1_9931 23 92
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 176 2 11 46 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 176 4 5 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 176 (accept_3_2 19 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  176 2 9 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 176 4 4 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 176 2 7 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 176 (accept_3_2 13 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 176 4 3 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 92 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 176 2 5 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 176
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 176 4 2 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 176 (accept_3_2 7 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 176
  2 3 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 92 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 92 176 4 1 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 92 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 176 2 1 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 176 (accept_3_2 1 92 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 92
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 91 176
  (Eq.refl Bool.true) (allA_of_3_0 86 91 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 90 176 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 90 176 2 43 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 90 176 (accept_3_2 85 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 176 2 42 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 176 (Polychromatic418967fa.accept_13_5_12_7_1_1080 83 90 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 176 2 41 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 81
  90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 176 2 40 45 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 176 (accept_3_2 79
  90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 176 2 39 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 176
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 77 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 90 176 2 38 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 90 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 90 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 176 2 37 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 176 (accept_3_2 73 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 176 2 36 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 176 (Polychromatic418967fa.accept_13_6_12_7_1_5131 71 90 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 176 2 35 45 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 176 2 34 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 90 176 (accept_3_2 67 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90
  176 2 33 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  90 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 90 176 2 32 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 90 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 176 2 31 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 176 (accept_3_2 61 90 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 176 2 30 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 176
  (Polychromatic418967fa.accept_19_2_14_5_1_5715 59 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 176 2 29 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 90 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 176 2 28 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 176 (accept_3_2 55 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 176 2 27 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 176 (Polychromatic418967fa.accept_23_7_21_15_1_9930 53 90
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 176 2 26 45 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 176 2 25 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 176 (accept_3_2 49 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90
  176 2 24 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  90 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 90 176 2 23 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 90 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 176 2 22 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 176 (accept_3_2 43 90 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 176 2 21 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 176
  (Polychromatic418967fa.accept_19_3_14_5_1_8597 41 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 176 2 20 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 176 2 19 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 176 (accept_3_2 37 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 176 2 18 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 176 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 90 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 176 2 17 45 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 176 2 16 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 176 (accept_3_2 31 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  176 2 15 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 176 (Polychromatic418967fa.accept_19_10_14_5_1_3079 29 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 90 176 2 14 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 176 2 13 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 176 (accept_3_2 25 90 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 176 2 12 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 176 2 11 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 176 2 10 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 176 (accept_3_2 19 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 176 2 9 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 90 176 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 90 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 176 2 8 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 176 2 7 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 176 (accept_3_2 13 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  176 2 6 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 176 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 176 2 5 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 176 2 4 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 176 (accept_3_2 7 90 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 176 2 3 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 176 2 2 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 176 2 1 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 176 (accept_3_2 1 90 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 89 176
  (Eq.refl Bool.true) (allA_succ_of_accept 87 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 89 176 (accept_3_2 85 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  89 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 89 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 89 176 (accept_3_2 82 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 89 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 89 176 (accept_3_2 79 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  89 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 89 176 (Polychromatic418967fa.accept_13_12_11_7_1_2491 77 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 89 176 (accept_3_2 76 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 89 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 89 176 (accept_3_2 73 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  89 176 (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 89 176 (Polychromatic418967fa.accept_19_14_13_5_1_9905 71 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 176 (accept_3_2 70 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 176
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 68 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 89 176 (accept_3_2 67 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  89 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 89 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 176 (accept_3_2 64 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 89 176 (accept_3_2 61 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 176 (accept_3_2 58 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 176 (accept_3_2 55 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 176 (Polychromatic418967fa.accept_21_12_5_8_1_9929 54 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 176 (accept_3_2 52 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 176 (accept_3_2 49 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 176 (accept_3_2 46 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 176
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 176 (accept_3_2 43 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 176 (accept_3_2 40 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 176 (accept_3_2 37 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 176 (Polychromatic418967fa.accept_17_2_4_6_1_1619 36 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 35 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 176 (accept_3_2 34 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 176 (accept_3_2 31 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 176 (accept_3_2 28 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 176 (accept_3_2 25 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 176 (accept_3_2 22 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 176 (accept_3_2 19 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 176 (accept_3_2 16 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 176 (accept_3_2 13 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 176 (accept_3_2 10 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 176
  (Polychromatic418967fa.accept_19_8_13_5_1_1889 8 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 176 (accept_3_2 7 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 89 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 176 (accept_3_2 4 89 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  89 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 176 (accept_3_2 1 89 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 176
  (allA_of_3_0 88 88 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 176 (allA_succ_of_accept 86 87 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 176 (accept_3_2 85 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 176 (accept_3_2 82 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 176 (accept_3_2 79 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 176 (accept_3_2 76 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 176 (accept_3_2 73 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 176 (accept_3_2 70 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 176 (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 176 (accept_3_2 67 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 176 (accept_3_2 64 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 176 (accept_3_2 61 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 176 (accept_3_2 58 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 176 (accept_3_2 55 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 176 (accept_3_2 52 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 176
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 176 (accept_3_2 49 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 176 (accept_3_2 46 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 176 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 176 (accept_3_2 43 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 176 (accept_3_2 40 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 176 (accept_3_2 37 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 176 (Polychromatic418967fa.accept_19_17_11_5_1_7092 36 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 176 (accept_3_2 34 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 176 (accept_3_2 31 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 176 (accept_3_2 28 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 176 (Polychromatic418967fa.accept_21_6_3_8_1_9928 27 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 176 (accept_3_2 25 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 176 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 176 (accept_3_2 22 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 176 (accept_3_2 19 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 176 (accept_3_2 16 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 176 (Polychromatic418967fa.accept_13_2_9_7_1_164 15 87 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 176
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 176 (accept_3_2 13 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 176 (accept_3_2 10 87 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 176 (accept_3_2 7 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 176 (accept_3_2 4 87 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 176 (accept_3_2 1 87 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 176
  (allA_succ_of_accept 85 86 176 (accept_3_2 85 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  176 2 42 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  86 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 176 2 41 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 176 (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 176 2 40 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 176 (accept_3_2 79 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 176 2 39 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 176
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 176 2 38 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 86 176 (Polychromatic418967fa.accept_13_10_8_7_1_1074 75 86 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 176 2 37 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 176 (accept_3_2 73 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 176 2 36 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 176 2 35 43 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 176 2 34 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 86 176 (accept_3_2 67 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86
  176 2 33 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  86 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 86 176 2 32 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 176 (Polychromatic418967fa.accept_17_12_1_6_1_3680 63 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 176 2 31 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 176 (accept_3_2 61 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 176 2 30 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 176 2 29 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 176 (Polychromatic418967fa.accept_14_1_2_8_1_655 57 86 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 176 2 28 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 176 (accept_3_2 55 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 176 2 27 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 176 2 26 43 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 176
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 176 2 25 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 176 (accept_3_2 49 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  176 2 24 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 176 2 23 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 176 2 22 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 176 (accept_3_2 43 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 176 2 21 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 176 2 20 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 176 (Polychromatic418967fa.accept_17_5_1_6_1_2615 39 86 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 176 2 19 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 176 (accept_3_2 37 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 176 2 18 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 176 2 17 43 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 176
  (Polychromatic418967fa.accept_19_14_10_5_1_3073 33 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 176 2 16 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 176 (accept_3_2 31 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  176 2 15 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 176 2 14 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 176 2 13 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 176 (accept_3_2 25 86 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 176 2 12 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 176 2 11 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 176 (Polychromatic418967fa.accept_19_2_10_5_1_5639 21 86 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 176 2 10 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 176 (accept_3_2 19 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 176 2 9 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 176 2 8 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 176
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 176 2 7 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 176 (accept_3_2 13 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  176 2 6 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 176 2 5 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 176 2 4 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 176 (accept_3_2 7 86 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 176 2 3 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 176 2 2 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 176 2 1 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 176 (accept_3_2 1 86 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 176
  (allA_of_3_0 85 85 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 176 (allA_succ_of_accept 83 84 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 176 2 41 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 84 176 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 84 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 176 4 20 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 176 (accept_3_2 79 84 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 176 2 39 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 176 (Polychromatic418967fa.accept_13_12_6_7_1_1071 77 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 176 4 19 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 176
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 176 2 37 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 176 (accept_3_2 73 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84
  176 4 18 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  84 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 84 176 2 35 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 84 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 176 4 17 21 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 176 (accept_3_2 67 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 176 2 33 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 176 4 16 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 176 (Polychromatic418967fa.accept_25_13_9_1_1_9927 63 84 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 176 2 31 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 176 (accept_3_2 61 84 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 176 4 15 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 176 (Polychromatic418967fa.accept_19_2_8_5_1_1885 59 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 176 2 29 42 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 176
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 57 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 176 4 14 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 176 (accept_3_2 55 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  176 2 27 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  84 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 176 4 13 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 176 2 25 42 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 176 (accept_3_2 49 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 176 4 12 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 176 2 23 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 176 4 11 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 176 (accept_3_2 43 84 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 176 2 21 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 176 (Polychromatic418967fa.accept_17_7_16_6_1_3705 41 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 176 4 10 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 176
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 39 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 176 2 19 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 176 (accept_3_2 37 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  176 4 9 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 176 2 17 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 176 4 8 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 176 (accept_3_2 31 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 176 2 15 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 176 4 7 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 176
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 176 2 13 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 176 (accept_3_2 25 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84
  176 4 6 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  84 176 (Polychromatic418967fa.accept_19_4_8_5_1_5636 23 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 84 176 2 11 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 84 176 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 176 4 5 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 176 (accept_3_2 19 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 176 2 9 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 176 4 4 21 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 176 2 7 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 176 (accept_3_2 13 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84
  176 4 3 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  84 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 84 176 2 5 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 84 176 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 84 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 176 4 2 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 176 (accept_3_2 7 84 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 176 2 3 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 84 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 84 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 176 4 1 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 176
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 3 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 176 2 1 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 176 (accept_3_2 1 84 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 176
  (allA_succ_of_accept 82 83 176 (accept_3_2 82 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 176 (accept_3_2 79 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 176
  (Polychromatic418967fa.accept_10_7_3_6_1_644 77 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 176 (accept_3_2 76 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 176 (accept_3_2 73 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 176 (accept_3_2 70 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 176 (accept_3_2 67 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 176 (accept_3_2 64 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 176 (accept_3_2 61 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 176
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 176 (accept_3_2 58 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 176 (Polychromatic418967fa.accept_18_2_11_14_1_69 56 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 176 (accept_3_2 55 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 176 (accept_3_2 52 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 176 (accept_3_2 49 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 176 (accept_3_2 46 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 176 (accept_3_2 43 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 176
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 176 (accept_3_2 40 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 176 (accept_3_2 37 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 176 (Polychromatic418967fa.accept_19_17_7_5_1_1883 36 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 176 (accept_3_2 34 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 176 (Polychromatic418967fa.accept_19_13_7_5_1_5712 32 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 176 (accept_3_2 31 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 83 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 176
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 176 (accept_3_2 28 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 176 (accept_3_2 25 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 176 (accept_3_2 22 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 176 (accept_3_2 19 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 83 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 176 (accept_3_2 16 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 176 (accept_3_2 13 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 176
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 176 (accept_3_2 10 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 176 (accept_3_2 7 83 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 176 (accept_3_2 4 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 176 (accept_3_2 1 83 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 176 (allA_of_3_0 82 82 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 176
  (allA_succ_of_accept 80 81 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 176 (accept_3_2 79 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 176 (accept_3_2 76 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 74 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 176 (accept_3_2 73 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 176 (accept_3_2 70 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 176
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 176 (accept_3_2 67 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 176 (accept_3_2 64 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 176
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 176 (accept_3_2 61 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 176 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 176 (accept_3_2 58 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 176
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 176 (Polychromatic418967fa.accept_13_4_3_7_1_2515 56 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 176 (accept_3_2 55 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 176 (accept_3_2 52 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 176
  (Polychromatic418967fa.accept_20_11_1_16_1_8513 51 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 176 (Polychromatic418967fa.accept_13_11_3_7_1_2513 50 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 176 (accept_3_2 49 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 176 (accept_3_2 46 81
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 176 (Polychromatic418967fa.accept_7_3_4_1_1_71
  45 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 176
  (Polychromatic418967fa.accept_24_20_9_8_1_9926 44 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 176 (accept_3_2 43 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 176 (accept_3_2 40 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 176 (accept_3_2 37 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 176 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 176 (accept_3_2 34 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 176 (accept_3_2 31 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 176 (accept_3_2 28 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 176 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 176 (accept_3_2 25 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 176 (accept_3_2 22 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 176 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 176
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 176 (accept_3_2 19 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 176 (accept_3_2 16 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 176
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 176 (accept_3_2 13 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 176 (accept_3_2 10 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 176
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 176 (accept_3_2 7 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 176 (accept_3_2 4 81 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  81 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 176 (accept_3_2 1 81 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 176
  (allA_succ_of_accept 79 80 176 (accept_3_2 79 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  176 2 39 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 176 (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 176 4 19 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 176 2 37 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 176 (accept_3_2 73 80 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 176 8 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 176 (Polychromatic418967fa.accept_25_21_5_1_1_9925
  71 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 176 2 35 40 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 176
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 80 176 4 17 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 80 176 (accept_3_2 67 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80
  176 2 33 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  80 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 80 176 16 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 80 176 (Polychromatic418967fa.accept_19_6_4_5_1_5650 63 80 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 176 2 31 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 176 (accept_3_2 61 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 176 4 15 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 176 (Polychromatic418967fa.accept_18_5_8_14_1_1282
  59 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 176 2 29 40 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 176 8 7 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 176 (accept_3_2 55 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  176 2 27 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  80 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 176 4 13 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 176 2 25 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 176 (accept_3_2 49 80 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 176 16 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 47
  80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 176 2 23 40 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 176
  (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 176 4 11 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 176 (accept_3_2 43 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  176 2 21 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 176 (Polychromatic418967fa.accept_18_5_8_14_1_1282 41 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 176 8 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 176 2 19 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 176 (accept_3_2 37 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 176 4 9 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 176 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 80 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 176 2 17 40 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 176 16 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 176 (accept_3_2 31 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  176 2 15 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 176 4 7 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 176 (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 176 2 13 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 176 (accept_3_2 25 80 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 176 8 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 176 2 11 40 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 176 4 5 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 176 (accept_3_2 19 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  176 2 9 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 176 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 176 16 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 80 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 176 2 7 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 176 (accept_3_2 13 80 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 176 4 3 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 176 2 5 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 176 8 1 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 176 (accept_3_2 7 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 176
  2 3 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 176 4 1 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 176 2 1 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 176 (accept_3_2 1 80 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 176 (allA_of_3_0 79 79 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 176
  (allA_succ_of_accept 77 78 176 (Polychromatic418967fa.accept_21_14_15_8_1_5281 77 78 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 176 2 38 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 75
  78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 176 2 37 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 176 (accept_3_2 73
  78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 176 2 36 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 176 2 35 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 78 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 78 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 176 2 34 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 176 (accept_3_2 67 78 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 176 2 33 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 176 2 32 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 176
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 176 2 31 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 176 (accept_3_2 61 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78
  176 2 30 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  78 176 (Polychromatic418967fa.accept_15_14_3_11_1_850 59 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 78 176 2 29 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 78 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 176 2 28 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 176 (accept_3_2 55 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 176 2 27 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 176 2 26 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 176 2 25 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 176 (accept_3_2 49 78 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 176 2 24 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 176 2 23 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 176 2 22 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 176 (accept_3_2 43 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  176 2 21 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 176 (Polychromatic418967fa.accept_19_3_2_5_1_5679 41 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 176 2 20 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 176 2 19 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 176 (accept_3_2 37 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 176 2 18 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 176 2 17 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 78 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 176 2 16 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 176 (accept_3_2 31 78 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 176 2 15 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 176 2 14 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 176 2 13 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 176 (accept_3_2 25 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  176 2 12 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 176 2 11 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 176 2 10 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 176 (accept_3_2 19 78 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 176 2 9 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 176 2 8 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 176 2 7 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 176 (accept_3_2 13 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  176 2 6 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 176 2 5 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 176 2 4 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 176 (accept_3_2 7 78 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 176 2 3 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 176 (Polychromatic418967fa.accept_20_5_18_16_1_1558 5 78 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 176 2 2 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 176 2 1 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 176 (accept_3_2 1 78 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 176
  (allA_succ_of_accept 76 77 176 (accept_3_2 76 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 176 (accept_3_2 73 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 176 (Polychromatic418967fa.accept_19_15_1_5_1_3013 72 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 176
  (Polychromatic418967fa.accept_10_1_7_6_1_91 71 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 176 (accept_3_2 70 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 176 (Polychromatic418967fa.accept_21_5_14_8_1_6818 68 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 176 (accept_3_2 67 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 77 176 11 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 77 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 176 (accept_3_2 64 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63
  77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 176 (accept_3_2 61 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 176 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 176 (Polychromatic418967fa.accept_17_8_9_6_1_7330 59 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 176 (accept_3_2 58 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 176
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 77 176 11 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 77 176 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 77 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 53 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 176 (accept_3_2 52 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 176 (accept_3_2 49 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 176 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 176 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 176 (accept_3_2 46 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 176 11 4 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 176 (accept_3_2 43 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 176 (Polychromatic418967fa.accept_17_8_9_6_1_7330
  42 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 176
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 176 (accept_3_2 40 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 176 (accept_3_2 37 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 176 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 176
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 176 (accept_3_2 34 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77
  176 11 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  77 176 (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 77 176 (accept_3_2 31 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 77 176 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 77 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 176 (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 176 (accept_3_2 28 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 176 (accept_3_2 25 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 176 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 77 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 77 176 11 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 176
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 176 (accept_3_2 19 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 176 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 176 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 176 (accept_3_2 16 77 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 176 (accept_3_2 13 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 176 (Polychromatic418967fa.accept_19_12_1_5_1_9924 12 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 77 176 11 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 77 176 (accept_3_2 10 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 77 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 176 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 176 (accept_3_2 7 77 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 176 (Polychromatic418967fa.accept_13_6_12_7_1_5131
  6 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 176
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 176 (accept_3_2 4 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 176 (accept_3_2 1 77 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 176 (allA_of_3_0 76 76 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 176 (allA_succ_of_accept 74 75
  176 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 176 (accept_3_2 73 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 176 (Polychromatic418967fa.accept_21_9_12_8_1_5255 72 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 176 (accept_3_2 70 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 176
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 68 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 176 (accept_3_2 67 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 176 (accept_3_2 64 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 176 (accept_3_2 61 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 176 (accept_3_2 58 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 176 (Polychromatic418967fa.accept_21_15_12_8_1_5275 57 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 176 (accept_3_2 55 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 176 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 176 (accept_3_2 52 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 176
  (Polychromatic418967fa.accept_17_16_7_6_1_7343 50 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 176 (accept_3_2 49 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 176 (accept_3_2 46 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 176 (accept_3_2 43 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 176 (accept_3_2 40 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 176 (accept_3_2 37 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 176 (Polychromatic418967fa.accept_19_17_18_5_1_3012 36 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 176 (accept_3_2 34 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 176 (accept_3_2 31 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 176 (accept_3_2 28 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 176 (accept_3_2 25 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 176 (accept_3_2 22 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 176 (accept_3_2 19 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 176 (accept_3_2 16 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 176 (accept_3_2 13 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 176 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 176 (accept_3_2 10 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 75 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 176 (accept_3_2 7 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 176 (accept_3_2 4 75 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 176 (accept_3_2 1 75 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 176 (allA_succ_of_accept
  73 74 176 (accept_3_2 73 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 176 2 36 37 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 176 2 35 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 176 2 34 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 176 (accept_3_2 67 74 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 176 2 33 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 74 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 176 2 32 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 176
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 176 2 31 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 176 (accept_3_2 61 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  176 2 30 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 176 2 29 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 176 2 28 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 176 (accept_3_2 55 74 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 176 2 27 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 176 2 26 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 176 2 25 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 176 (accept_3_2 49 74 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 176 2 24 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 74 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 176 2 23 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 176 2 22 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 176 (accept_3_2 43 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  176 2 21 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 176 2 20 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 176 2 19 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 176 (accept_3_2 37 74 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 176 2 18 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 176 2 17 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 176 2 16 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 176 (accept_3_2 31 74 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 176 2 15 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 176 2 14 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 176
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 74 176 2 13 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 74 176 (accept_3_2 25 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 176 2 12 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 74 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 176 2 11 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 176 2 10 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 176 (accept_3_2 19
  74 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 176 2 9 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 74 176 2 8 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 74 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 176 2 7 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 176 (accept_3_2 13 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 74 176 2 6 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 74 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 176 2 5 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 176 (Polychromatic418967fa.accept_25_9_24_1_1_9923 9
  74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 176 2 4 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 176 (accept_3_2 7 74
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 176 2 3 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 176 2 2 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 176 2 1 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 176 (accept_3_2 1 74 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  176 (allA_of_3_0 73 73 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 176 (allA_succ_of_accept 71 72 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 71 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 176 2 35 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 176 4 17 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 176 (accept_3_2 67 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 176 2 33 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 176 (Polychromatic418967fa.accept_27_11_18_14_1_9922 65 72
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 176 8 8 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 176
  (Polychromatic418967fa.accept_19_6_15_5_1_5697 63 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 176 2 31 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 176 (accept_3_2 61 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  176 4 15 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 176 2 29 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 176 (Polychromatic418967fa.accept_14_1_2_8_1_655 57 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 176 8 7 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 176 (accept_3_2 55 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 176 2 27 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 176 (Polychromatic418967fa.accept_15_8_12_11_1_1570
  53 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 176 4 13 18 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 176 2 25 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 176 (accept_3_2 49 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72
  176 8 6 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  72 176 (Polychromatic418967fa.accept_19_9_15_5_1_5666 47 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 72 176 2 23 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 72 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 176 4 11 18 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 176 (accept_3_2 43 72 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 176 2 21 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 176 8 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 176 (Polychromatic418967fa.accept_17_5_4_6_1_7342 39 72 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 176 2 19 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 176 (accept_3_2 37 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 176 4 9 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 72 176 (Polychromatic418967fa.accept_23_12_3_15_1_9921 35 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 176 2 17 36 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 176
  (Polychromatic418967fa.accept_21_12_9_8_1_2370 33 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 176 8 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 176 (accept_3_2 31 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  176 2 15 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 176 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 176 4 7 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 176 2 13 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 176 (accept_3_2 25 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 176 8 3 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 176 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 72
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 176 2 11 36 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 176 4 5 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 176 (accept_3_2 19 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  176 2 9 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 176 8 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 176 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 176 2 7 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 176 (accept_3_2 13 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 176 4 3 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 72 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 176 2 5 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 176
  (Polychromatic418967fa.accept_19_9_15_5_1_5666 9 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 176 8 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 176 (accept_3_2 7 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 176
  2 3 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  176 (Polychromatic418967fa.accept_17_5_4_6_1_7342 5 72 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 176 4 1 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 176 2 1 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 176 (accept_3_2 1 72 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 176 (allA_succ_of_accept 70 71 176 (accept_3_2 70 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 176 (Polychromatic418967fa.accept_19_11_14_5_1_5629 68 71
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 176 (accept_3_2 67 71 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 66
  71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 176 (accept_3_2 64 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 176 (accept_3_2 61 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 176
  (Polychromatic418967fa.accept_19_2_14_5_1_5715 59 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 176 (accept_3_2 58 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 176 (accept_3_2 55 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 176 (Polychromatic418967fa.accept_19_16_14_5_1_9920 54 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 176
  (Polychromatic418967fa.accept_13_1_6_7_1_550 53 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 176 (accept_3_2 52 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 176 (accept_3_2 49 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 176 (accept_3_2 46 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 176 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 176 (accept_3_2 43 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 176
  (Polychromatic418967fa.accept_19_3_14_5_1_8597 41 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 176 (accept_3_2 40 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 176 (accept_3_2 37 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 176 (Polychromatic418967fa.accept_19_17_14_5_1_8561 36 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 176
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 176 (accept_3_2 34 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 176 (accept_3_2 31 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 176 (accept_3_2 28 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 176 (accept_3_2 25 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 176
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 176 (accept_3_2 22 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 176 (accept_3_2 19 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 176 (Polychromatic418967fa.accept_17_1_3_6_1_3672 18 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 176
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 176 (accept_3_2 16 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 176 (accept_3_2 13 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 176 (accept_3_2 10 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 176 (Polychromatic418967fa.accept_19_8_14_5_1_9919 8 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 176 (accept_3_2 7 71 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 176
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 176 (accept_3_2 4 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 71 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 176 (accept_3_2 1 71 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 176
  (allA_of_3_0 70 70 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 176 (allA_succ_of_accept 68 69 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 176 (accept_3_2 67 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 176 (accept_3_2 64 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 176 (accept_3_2 61 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 176 (Polychromatic418967fa.accept_26_8_17_20_1_9918 60 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 176 (accept_3_2 58 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 176 (accept_3_2 55 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 176 (accept_3_2 52 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 176
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 176 (accept_3_2 49 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 176 (accept_3_2 46 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 176 (accept_3_2 43 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 176 (accept_3_2 40 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 176 (accept_3_2 37 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 176 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 176 (accept_3_2 34 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 176
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 176 (accept_3_2 31 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 176 (accept_3_2 28 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 176 (Polychromatic418967fa.accept_19_8_12_5_1_7122 27 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 176 (accept_3_2 25 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 176 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 176 (accept_3_2 22 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 176 (accept_3_2 19 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 176 (accept_3_2 16 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 176
  (Polychromatic418967fa.accept_21_14_6_8_1_1285 14 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 176 (accept_3_2 13 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 176 (accept_3_2 10 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 176 (accept_3_2 7 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 176 (accept_3_2 4 69 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 176 (accept_3_2 1 69 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 176 (allA_succ_of_accept 67 68
  176 (accept_3_2 67 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 176 2 33 34 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 176
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 176 4 16 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 68 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 176 2 31 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 176 (accept_3_2 61 68 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 176 4 15 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 176 2 29 34 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 176
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 57 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 176 4 14 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 176 (accept_3_2 55 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  176 2 27 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 176 4 13 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 176 (Polychromatic418967fa.accept_19_13_11_5_1_5692 51 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 176 2 25 34 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 176 (accept_3_2 49 68 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 176 4 12 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 176
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 176 2 23 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 176 4 11 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 176 (accept_3_2 43 68 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 176 2 21 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 176 4 10 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 176 2 19 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 176 (accept_3_2 37 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  176 4 9 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 176 2 17 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 176 4 8 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 176 (accept_3_2 31 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 176 2 15 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 176 (Polychromatic418967fa.accept_19_10_11_5_1_7093
  29 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 176 4 7 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 176 2 13 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 176 (accept_3_2 25 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  176 4 6 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 176 2 11 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 176 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 176 4 5 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 176 (accept_3_2 19 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 176 2 9 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 176 4 4 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 176
  (Polychromatic418967fa.accept_19_15_11_5_1_5713 15 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 176 2 7 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 176 (accept_3_2 13 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  176 4 3 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 176 2 5 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 176 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 68 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 176 4 2 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 176 (accept_3_2 7 68 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 176 2 3 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 68 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 176 4 1 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 176 2 1 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 176 (accept_3_2 1 68 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 176 (allA_of_3_0 67 67 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 176 (allA_succ_of_accept 65 66 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 176 2 32 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 176 2 31 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 176 (accept_3_2 61 66 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 176 2 30 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 176 (Polychromatic418967fa.accept_17_8_15_6_1_4889 59 66 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 176 2 29 33 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 176 2 28 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 66 176 11 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 66 176 2 27 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 176 2 26 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 51
  66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 176 2 25 33 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 176 (accept_3_2 49
  66 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 176 2 24 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 176 2 23 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 176 22 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 176 (accept_3_2 43 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 66 176 2 21 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 66 176 (Polychromatic418967fa.accept_20_1_6_16_1_6991 41 66 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 176 2 20 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 176 2 19 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 176 (accept_3_2 37 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  176 2 18 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 176 2 17 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 176 11 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 176 2 16 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 176 (accept_3_2 31 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 176 2 15 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 176 2 14 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 27
  66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 176 2 13 33 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 176 (accept_3_2 25
  66 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 176 2 12 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 176 22 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 176 2 10 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 176 (accept_3_2 19 66 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 176 2 9 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 66 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 176 2 8 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 176
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 176 2 7 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 176 (accept_3_2 13 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  176 2 6 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66
  176 11 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66
  176 2 5 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  66 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 66 176 2 4 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 66 176 (accept_3_2 7 66 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 176 2 3 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 176 2 2 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 176 2 1 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 176 (accept_3_2 1 66 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 176 (allA_succ_of_accept 64 65 176
  (accept_3_2 64 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 65 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 176 (accept_3_2 61 65 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 176 (accept_3_2 58 65
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 176
  (Polychromatic418967fa.accept_18_2_11_14_1_69 56 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 176 (accept_3_2 55 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 176 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 176 (accept_3_2 52 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 176 (accept_3_2 49 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 176 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 176 (accept_3_2 46 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 176 (accept_3_2 43 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 176 (accept_3_2 40 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 176 (accept_3_2 37 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 176 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 176 (accept_3_2 34 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 176
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 176 (accept_3_2 31 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 176 (accept_3_2 28 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 176 (accept_3_2 25 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 176 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 176 (accept_3_2 22 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 176 (accept_3_2 19 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 176 (Polychromatic418967fa.accept_20_18_5_16_1_5425 18 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 176 (accept_3_2 16 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 176 (accept_3_2 13 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 176 (accept_3_2 10 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 176 (accept_3_2 7 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 176 (Polychromatic418967fa.accept_18_5_11_14_1_7203 5 65 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 176 (accept_3_2 4 65 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  65 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 176 (accept_3_2 1 65 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 176 (allA_of_3_0 64 64 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 176 (allA_succ_of_accept 62 63 176
  (Polychromatic418967fa.accept_14_6_7_8_1_624 62 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 176 (accept_3_2 61 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 176 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 176 (accept_3_2 58 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 176
  (Polychromatic418967fa.accept_13_4_11_7_1_558 56 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 176 (accept_3_2 55 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 176 (accept_3_2 52 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 176 (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 176
  (Polychromatic418967fa.accept_24_2_15_8_1_6377 50 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 176 (accept_3_2 49 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 176 (accept_3_2 46 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 176 (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 176
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 176 (accept_3_2 43 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 176 (accept_3_2 40 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 176 (accept_3_2 37 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 176 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 176 (accept_3_2 34 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 176 (Polychromatic418967fa.accept_19_14_6_5_1_9917 33 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 176
  (Polychromatic418967fa.accept_23_9_17_15_1_9916 32 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 176 (accept_3_2 31 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 176 (accept_3_2 28 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 176 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 176
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 26 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 176 (accept_3_2 25 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 176 (Polychromatic418967fa.accept_18_6_9_14_1_9915 24 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 176 (accept_3_2 22 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 176 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 176
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 176 (accept_3_2 19 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 176 (accept_3_2 16 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 176 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 176
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 176 (accept_3_2 13 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 176 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 176 (accept_3_2 10 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 176 (accept_3_2 7 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 176 (accept_3_2 4 63 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 176 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 176 (Polychromatic418967fa.accept_17_2_12_6_1_3737
  2 63 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 176 (accept_3_2 1 63
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 176 (allA_succ_of_accept 61 62 176
  (accept_3_2 61 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 176 2 30 31 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 176 2 29 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 176 2 28 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 176 (accept_3_2 55 62 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 176 2 27 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 62 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 176 2 26 31 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 176 2 25 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 176 (accept_3_2 49 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  176 2 24 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 176 2 23 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 176 (Polychromatic418967fa.accept_23_22_16_15_1_9914 45 62 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 176 2 22 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 176 (accept_3_2 43 62 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 176 2 21 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 41 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 176 2 20 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 176 2 19 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 176 (accept_3_2 37 62 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 176 2 18 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 176 2 17 31 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 176 2 16 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 176 (accept_3_2 31 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  176 2 15 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 176 2 14 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 176 (Polychromatic418967fa.accept_23_4_16_15_1_9913 27 62 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 176 2 13 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 176 (accept_3_2 25 62 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 176 2 12 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 176 2 11 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 176 2 10 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 176 (accept_3_2 19 62 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 176 2 9 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 176 2 8 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 176
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 176 2 7 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 176 (accept_3_2 13 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  176 2 6 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 176 2 5 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 176 2 4 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 176 (accept_3_2 7 62 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 176 2 3 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 176 2 2 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 176 2 1 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 176 (accept_3_2 1 62 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 176 (allA_of_3_0 61 61 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 176 (allA_succ_of_accept 59 60 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 176 2 29 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 176 4 14 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 176 (accept_3_2 55 60 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 176 2 27 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 176 4 13 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 176
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 176 2 25 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 176 (accept_3_2 49 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  176 4 12 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 176 2 23 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 176 4 11 15 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 176 (accept_3_2 43 60 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 176 2 21 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 176
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 41 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 176 4 10 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 176 2 19 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 176 (accept_3_2 37 60 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 176 4 9 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 176 2 17 30 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 176 4 8 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 176 (accept_3_2 31 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  176 2 15 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 176 4 7 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 176 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 60 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 176 2 13 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 176 (accept_3_2 25 60 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 176 4 6 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 176 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 60 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 176 2 11 30 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 176 4 5 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 176 (accept_3_2 19 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  176 2 9 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 176 4 4 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 176 (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 60 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 176 2 7 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 176 (accept_3_2 13 60 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 176 4 3 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 60 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 176 2 5 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 176
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 176 4 2 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 176 (accept_3_2 7 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 176
  2 3 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 176 4 1 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 176 2 1 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 176 (accept_3_2 1 60 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 176
  (allA_succ_of_accept 58 59 176 (accept_3_2 58 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 176 (Polychromatic418967fa.accept_19_18_2_5_1_5682 56 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 176 (accept_3_2 55 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 176 (accept_3_2 52 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 176 (accept_3_2 49 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 176 (Polychromatic418967fa.accept_15_3_14_11_1_1579 48 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 176 (accept_3_2 46 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 176 (accept_3_2 43 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 176 (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 59 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 176
  (Polychromatic418967fa.accept_19_3_2_5_1_5679 41 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 176 (accept_3_2 40 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 176 (accept_3_2 37 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 176 (Polychromatic418967fa.accept_19_17_2_5_1_7085 36 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 176
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 176 (accept_3_2 34 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 176 (accept_3_2 31 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 176
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 176 (accept_3_2 28 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 176 (accept_3_2 25 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 176 (Polychromatic418967fa.accept_21_3_17_8_1_8402 24 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 176 (accept_3_2 22 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 176 (Polychromatic418967fa.accept_21_20_17_8_1_9912 20 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 176 (accept_3_2 19 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 176
  (Polychromatic418967fa.accept_19_17_2_5_1_7085 17 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 176 (accept_3_2 16 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 176 (accept_3_2 13 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 176 (accept_3_2 10 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 176 (Polychromatic418967fa.accept_18_8_5_14_1_3353 8 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 176 (accept_3_2 7 59 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 176 (Polychromatic418967fa.accept_25_6_9_1_1_9911 6 59 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 176 (accept_3_2 4 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 176 (accept_3_2 1 59 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 176 (allA_of_3_0
  58 58 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 176 (allA_succ_of_accept 56 57 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 176 (accept_3_2 55 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 176 (accept_3_2 52 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 176
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 50 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 176 (accept_3_2 49 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 176 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 176 (accept_3_2 46 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 45 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 176 (accept_3_2 43 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 176 (accept_3_2 40 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 176 (Polychromatic418967fa.accept_20_19_17_16_1_2732 39 57 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 176 (accept_3_2 37 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 176 (Polychromatic418967fa.accept_23_13_11_15_1_9910 36 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 176 (accept_3_2 34 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 176
  (Polychromatic418967fa.accept_26_6_5_20_1_9909 32 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 176 (accept_3_2 31 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 176 (accept_3_2 28 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 176 (accept_3_2 25 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 176 (accept_3_2 22 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 176 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 176 (accept_3_2 19 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 176 (accept_3_2 16 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 176
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 57 176 (accept_3_2 13 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 176 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 57 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 176 (accept_3_2 10 57 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 176 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9
  57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 176 (accept_3_2 7 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 176 (accept_3_2 4 57 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 57 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 176 (accept_3_2 1 57 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 176)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 176 (allA_succ_of_accept 55 56 176 (accept_3_2 55 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 176 2 27 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 176 4 13 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 176 2 25 28 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 176 (accept_3_2 49
  56 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 176 8 6 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 176
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 176 2 23 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 176 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 56 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 176 4 11 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 176 (accept_3_2 43 56 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 176 2 21 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 176 (Polychromatic418967fa.accept_23_18_10_15_1_4784 41 56
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 176 8 5 7 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 176 2 19 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 176 (accept_3_2 37 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  176 4 9 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 176 2 17 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 176 8 4 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 176 (accept_3_2 31 56 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 176 2 15 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 176 (Polychromatic418967fa.accept_13_3_4_7_1_1711
  29 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 176 4 7 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 176
  (Polychromatic418967fa.accept_21_6_14_8_1_9908 27 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 176 2 13 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 176 (accept_3_2 25 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  176 8 3 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 176 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 176 2 11 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 176 4 5 14 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 176 (accept_3_2 19 56 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 176 2 9 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 176 8 2 7 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 176
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 176 2 7 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 176 (accept_3_2 13 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  176 4 3 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 176 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 176 2 5 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 176 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 56 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 176 8 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 176 (accept_3_2 7 56 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 176 2 3 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 176 (Polychromatic418967fa.accept_21_5_14_8_1_6818 5 56 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 176 4 1 14 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 176 2 1 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 176 (accept_3_2 1 56 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 176 (allA_of_3_0 55 55 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 176 (allA_succ_of_accept 53 54 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 176 2 26 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 176 2 25 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 176 (accept_3_2 49 54 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 176 2 24 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 176 (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 54 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 176 2 23 27 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 176 2 22 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 176 (accept_3_2 43 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  176 2 21 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 176 2 20 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 176 2 19 27 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 176 (accept_3_2 37 54 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 176 2 18 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 176
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 176 2 17 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 176 2 16 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 176 (accept_3_2 31 54 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 176 2 15 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 176 (Polychromatic418967fa.accept_19_10_16_5_1_8562 29 54
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 176 2 14 27 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 176 2 13 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 176 (accept_3_2 25 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  176 2 12 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 176 (Polychromatic418967fa.accept_25_23_4_1_1_9907 23 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 176 2 11 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 176 2 10 27 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 176 (accept_3_2 19 54 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 176 2 9 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 176 2 8 27 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 176
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 176 2 7 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 176 (accept_3_2 13 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  176 2 6 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 176 2 5 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 176 2 4 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 176 (accept_3_2 7 54 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 176 2 3 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 176 2 2 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 176 2 1 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 176 (accept_3_2 1 54 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  176)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 176 (allA_succ_of_accept 52 53 176 (accept_3_2
  52 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 176 (accept_3_2 49 53 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 47
  53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 176 (accept_3_2 46 53
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 176
  (Polychromatic418967fa.accept_19_6_15_5_1_5697 44 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 176 (accept_3_2 43 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 176 (Polychromatic418967fa.accept_21_20_11_8_1_9906 41 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 176 (accept_3_2 40 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 176 (accept_3_2 37 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 176 (Polychromatic418967fa.accept_19_17_15_5_1_7096 36 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 176 (accept_3_2 34 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 176
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 176 (accept_3_2 31 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 176 (accept_3_2 28 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 176 (accept_3_2 25 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 176 (Polychromatic418967fa.accept_19_4_15_5_1_3043 23 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 176 (accept_3_2 22 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 176 (accept_3_2 19 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 176 (accept_3_2 16 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 176 (accept_3_2 13 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 176 (accept_3_2 10 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 176 (accept_3_2 7 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 176 (accept_3_2 4 53 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  53 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 176 (accept_3_2 1 53 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 176)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 176 (allA_of_3_0 52 52 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 176
  (allA_succ_of_accept 50 51 176 (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 176 (accept_3_2 49 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 176 (accept_3_2 46 51
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 176 (accept_3_2 43 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 176 (accept_3_2 40 51
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 176 (Polychromatic418967fa.accept_9_3_6_5_1_63
  39 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 176 (accept_3_2 37 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 176 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 176 (accept_3_2 34 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 51 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 176 (accept_3_2 31 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 176 (accept_3_2 28 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 176 (accept_3_2 25 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 176 (accept_3_2 22 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 176
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 176 (accept_3_2 19 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 176 (accept_3_2 16 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 176 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 51 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 176
  (Polychromatic418967fa.accept_19_14_13_5_1_9905 14 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 176 (accept_3_2 13 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 176 (accept_3_2 10 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 51 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 176 (accept_3_2 7 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 176 (accept_3_2 4 51 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 176 (accept_3_2 1 51 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 176)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 176 (allA_succ_of_accept 49 50 176 (accept_3_2 49 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 176 2 24 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 50 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 176 2 23 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 176 (Polychromatic418967fa.accept_19_7_12_5_1_7123
  45 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 176 2 22 25 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 176 (accept_3_2 43
  50 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 176 2 21 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 176
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 176 2 20 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 176 (Polychromatic418967fa.accept_15_9_5_11_1_5416 39 50 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 176 2 19 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 176 (accept_3_2 37 50 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 176 2 18 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 176 2 17 25 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 176
  (Polychromatic418967fa.accept_27_6_23_14_1_9904 33 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 176 2 16 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 176 (accept_3_2 31 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  176 2 15 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 176 2 14 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 176 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 50 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 176 2 13 25 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 176 (accept_3_2 25 50 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 176 2 12 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 176 2 11 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 176 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 50 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 176 2 10 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 176 (accept_3_2 19 50 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 176 2 9 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 176 2 8 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 176
  (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 176 2 7 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 176 (accept_3_2 13 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  176 2 6 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 176 2 5 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 176 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 50 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 176 2 4 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 176 (accept_3_2 7 50 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 176 2 3 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 176 2 2 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 176
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 176 2 1 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 176 (accept_3_2 1 50 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  176)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 176 (allA_of_3_0 49 49 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 176 (allA_succ_of_accept 47 48 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 176 2 23 24 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 176
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 176 4 11 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 176 (accept_3_2 43 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  176 2 21 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 176 (Polychromatic418967fa.accept_13_2_9_7_1_164 41 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 176 8 5 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 176 (Polychromatic418967fa.accept_18_3_12_14_1_2232 39 48 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 176 2 19 24 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 176 (accept_3_2 37 48 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 176 4 9 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 35
  48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 176 2 17 24 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 176 16 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 176 (accept_3_2 31 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  176 2 15 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 176 4 7 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 176 (Polychromatic418967fa.accept_19_8_10_5_1_9903 27 48 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 176 2 13 24 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 176 (accept_3_2 25 48 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 176 8 3 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 176 2 11 24 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 176
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 176 4 5 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 176 (accept_3_2 19 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  176 2 9 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 176 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 176 16 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 176 2 7 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 176 (accept_3_2 13 48 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 176 4 3 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 176 2 5 24 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 176 8 1 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 176 (accept_3_2 7 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 176
  2 3 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 176 4 1 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 176 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 176 2 1 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 176 (accept_3_2 1 48 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 176)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 176 (allA_succ_of_accept 46
  47 176 (accept_3_2 46 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 176 (accept_3_2 43 47 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 176 (accept_3_2 40 47
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 176 (accept_3_2 37 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 176 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 176 (accept_3_2 34 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 176 (accept_3_2 31 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 176 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 176 (accept_3_2 28 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 176 (accept_3_2 25 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 176 (accept_3_2 22 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 176 (accept_3_2 19 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 176 (accept_3_2 16 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 176 (accept_3_2 13 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 176 (accept_3_2 10 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 176 (accept_3_2 7 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 176 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 47 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 176 (accept_3_2 4 47 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  47 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 176 (accept_3_2 1 47 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 176))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  176 (allA_of_3_0 46 46 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 176 (allA_succ_of_accept 44 45 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 176 (accept_3_2 43 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 176 (accept_3_2 40 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 176
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 38 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 176 (accept_3_2 37 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 176 (Polychromatic418967fa.accept_19_17_7_5_1_1883 36 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 176 (accept_3_2 34 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 176
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 176 (accept_3_2 31 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 176 (accept_3_2 28 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 176 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 176
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 176 (accept_3_2 25 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 176 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 176 (accept_3_2 22 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 176 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 176
  (Polychromatic418967fa.accept_24_20_21_8_1_9902 20 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 176 (accept_3_2 19 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 176 (accept_3_2 16 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 176 (Polychromatic418967fa.accept_20_15_5_16_1_4026 15 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 176 (accept_3_2 13 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 176 (accept_3_2 10 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 176
  (Polychromatic418967fa.accept_27_8_18_14_1_9901 8 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 176 (accept_3_2 7 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  176 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 176 (accept_3_2 4 45 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 176 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 45 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 176 (accept_3_2 1 45 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 176))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  176 (allA_succ_of_accept 43 44 176 (accept_3_2 43 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 176 2 21 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 176 4 10 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 44 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 176 2 19 22 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 176 (accept_3_2 37 44 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 176 4 9 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 35
  44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 176 2 17 22 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 44 176 11 3 4 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 44 176 4 8 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 176 (accept_3_2 31
  44 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 176 2 15 22 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 176 4 7 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 176 2 13 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 176 (accept_3_2 25 44 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 176 4 6 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 44 176 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 44 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 176 22 1 2 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 176
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 176 4 5 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 176 (accept_3_2 19 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  176 2 9 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 176 4 4 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 176 2 7 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 176 (accept_3_2 13 44 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 176 4 3 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 11 44 176 11 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 44 176 2 5 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 44 176 (Polychromatic418967fa.accept_24_9_20_8_1_9900 9 44 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 176 4 2 11 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 176 (accept_3_2 7 44 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 176 2 3 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 44 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 176 4 1 11 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 176
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 176 2 1 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 176 (accept_3_2 1 44 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  176)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 176 (allA_of_3_0 43 43 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 176 (allA_succ_of_accept 41 42 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 42 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 176 2 20 21 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 176 2 19 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 176 (accept_3_2 37 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  176 2 18 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 176 2 17 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 176 2 16 21 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 176 (accept_3_2 31 42 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 176 2 15 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 176
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 176 2 14 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 176 2 13 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 176 (accept_3_2 25 42 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 176 2 12 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 176 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 42 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 176 2 11 21 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 176 2 10 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 176 (accept_3_2 19 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  176 2 9 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 176 2 8 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 176 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 176 2 7 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 176 (accept_3_2 13 42 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 176 2 6 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 176 2 5 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 176 2 4 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 176 (accept_3_2 7 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 176
  2 3 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  176 (Polychromatic418967fa.accept_23_5_19_15_1_9899 5 42 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 176 2 2 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 176 2 1 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 176 (accept_3_2 1 42 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 42 176)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 176 (allA_succ_of_accept
  40 41 176 (accept_3_2 40 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 176 (accept_3_2 37 41 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 176 (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 176
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 176 (accept_3_2 34 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 176 (accept_3_2 31 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 176
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 176 (accept_3_2 28 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 176 (accept_3_2 25 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 176 (Polychromatic418967fa.accept_25_24_16_1_1_9898 24 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 176 (accept_3_2 22 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 176 (Polychromatic418967fa.accept_19_1_3_5_1_3092 20 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 176 (accept_3_2 19 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 176 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 176
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 176 (accept_3_2 16 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 176 (accept_3_2 13 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 176
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 176 (accept_3_2 10 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 176 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 176 (accept_3_2 7 41 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 176 (Polychromatic418967fa.accept_19_6_3_5_1_9897 6 41 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 176 (accept_3_2 4 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 176 (accept_3_2 1 41 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 176))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 176 (allA_of_3_0 40 40 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 176 (allA_succ_of_accept 38 39 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 176 (accept_3_2 37 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 176 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 176 (accept_3_2 34 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 176
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 176 (accept_3_2 31 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 176 (accept_3_2 28 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 39 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 176
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 176 (accept_3_2 25 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 176 (accept_3_2 22 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 176 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 39 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 176 (accept_3_2 19 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 176 (accept_3_2 16 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 176
  (Polychromatic418967fa.accept_23_14_16_15_1_9896 14 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 39 176 (accept_3_2 13 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 176 (accept_3_2 10 39 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 176 (Polychromatic418967fa.accept_18_9_3_14_1_3361
  9 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 176 (accept_3_2 7 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 176 (accept_3_2 4 39 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 176 (accept_3_2 1 39 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 176))))))))))))))))))))))))))))))))))))))) (allB_succ 38 176
  (allA_succ_of_accept 37 38 176 (accept_3_2 37 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  176 2 18 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 176 2 17 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 176 2 16 19 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 176 (accept_3_2 31 38 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 176 2 15 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 176
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 176 2 14 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 176 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 38 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 176 2 13 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 176 (accept_3_2 25 38 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 176 2 12 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 176 2 11 19 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 176
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 176 2 10 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 176 (accept_3_2 19 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  176 2 9 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 176 2 8 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 38 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 176 2 7 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 176 (accept_3_2 13 38 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 176 2 6 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 176 2 5 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 176 2 4 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 176 (accept_3_2 7 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 176
  2 3 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 176 2 2 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 176 2 1 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 176 (accept_3_2 1 38 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 176)))))))))))))))))))))))))))))))))))))) (allB_succ 37 176 (allA_of_3_0 37 37 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 176 (allA_succ_of_accept 35 36 176
  (Polychromatic418967fa.accept_15_5_6_11_1_854 35 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 176 2 17 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 176 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 36 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 176 4 8 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 176 (accept_3_2 31 36 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 176 2 15 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 176 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 36 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 176 4 7 9 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 176
  (Polychromatic418967fa.accept_21_6_15_8_1_9895 27 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 176 2 13 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 176 (accept_3_2 25 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  176 4 6 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 176 (Polychromatic418967fa.accept_21_2_15_8_1_9894 23 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 176 2 11 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 176 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 176 4 5 9 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 176 (accept_3_2 19 36 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 176 2 9 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 176 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 36 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 176 4 4 9 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 176
  (Polychromatic418967fa.accept_19_15_17_5_1_3052 15 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 176 2 7 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 176 (accept_3_2 13 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  176 4 3 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 176 (Polychromatic418967fa.accept_19_11_17_5_1_8609 11 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 176 2 5 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 176 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 36 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 176 4 2 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 176 (accept_3_2 7 36 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 176 2 3 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 176 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 36 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 176 4 1 9 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 176
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 176 2 1 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 176 (accept_3_2 1 36 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  176)))))))))))))))))))))))))))))))))))) (allB_succ 35 176 (allA_succ_of_accept 34 35 176 (accept_3_2 34 35 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 176
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 176 (accept_3_2 31 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 176 (accept_3_2 28 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 176 (accept_3_2 25 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 176 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 176 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 35 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 176 (accept_3_2 22 35 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 176
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 176 (accept_3_2 19 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 176 (Polychromatic418967fa.accept_20_18_15_16_1_9893 18 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 176 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 176 (accept_3_2 16 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 176 (accept_3_2 13 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 176 (accept_3_2 10 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 176
  (Polychromatic418967fa.accept_13_8_9_7_1_530 8 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 176 (accept_3_2 7 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 176 (Polychromatic418967fa.accept_17_5_1_6_1_2615 5 35 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 176 (accept_3_2 4 35 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 176 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 176 (accept_3_2 1 35 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 176))))))))))))))))))))))))))))))))))) (allB_succ 34 176
  (allA_of_3_0 34 34 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 176 (allA_succ_of_accept 32 33 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 176 (accept_3_2 31 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 176 (accept_3_2 28 33 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 176 (accept_3_2 25 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 176 11 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 33 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 176
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 176 (accept_3_2 19 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 176 (accept_3_2 16 33 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 176 (Polychromatic418967fa.accept_21_15_12_8_1_5275 15 33 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 176
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 176 (accept_3_2 13 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 33 176 11 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 33 176 (accept_3_2 10 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 176 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 33 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 176 (accept_3_2 7 33 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 176 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 176
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 176 (accept_3_2 4 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 33 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 176 (accept_3_2 1 33 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 176))))))))))))))))))))))))))))))))) (allB_succ 32 176 (allA_succ_of_accept 31 32 176
  (accept_3_2 31 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 176 2 15 16 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 176
  (Polychromatic418967fa.accept_19_10_13_5_1_3091 29 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 176 4 7 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 176 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 32 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 176 2 13 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 176 (accept_3_2 25 32 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 176 8 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 176 (Polychromatic418967fa.accept_25_23_7_1_1_9892 23 32 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 176 2 11 16 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 176
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 176 4 5 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 176 (accept_3_2 19 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  176 2 9 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 176 16 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 176 (Polychromatic418967fa.accept_25_15_7_1_1_9891 15 32 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 176 2 7 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 176 (accept_3_2 13 32 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 176 4 3 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 176 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 176 2 5 16 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 176
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 176 8 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 176 (accept_3_2 7 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 176
  2 3 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 176 4 1 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 176 2 1 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 176 (accept_3_2 1 32 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 176)))))))))))))))))))))))))))))))) (allB_succ 31 176 (allA_of_3_0 31 31 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 176 (allA_succ_of_accept 29 30 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 176 2 14 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 176 2 13 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 176 (accept_3_2 25 30 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 176 2 12 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 176 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 30 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 176 2 11 15 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 176 2 10 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 176 (accept_3_2 19 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  176 2 9 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 176 2 8 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 30 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 176 2 7 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 176 (accept_3_2 13 30 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 176 2 6 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 176 2 5 15 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 176
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 176 2 4 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 176 (accept_3_2 7 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 176
  2 3 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  176 (Polychromatic418967fa.accept_20_5_10_16_1_9890 5 30 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 176 2 2 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 176 2 1 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 176 (accept_3_2 1 30 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 176)))))))))))))))))))))))))))))) (allB_succ 29 176 (allA_succ_of_accept 28 29 176
  (accept_3_2 28 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 176 (accept_3_2 25 29 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 176 (Polychromatic418967fa.accept_10_3_9_6_1_94 23
  29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 176 (accept_3_2 22 29
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 176
  (Polychromatic418967fa.accept_18_2_11_14_1_69 20 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 176 (accept_3_2 19 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 176 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 176 (accept_3_2 16 29 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 176 (accept_3_2 13 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 176 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 29 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 176 (accept_3_2 10 29 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 176 (accept_3_2 7 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 176 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 29 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 176 (accept_3_2 4 29 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  29 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 176 (accept_3_2 1 29 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 176))))))))))))))))))))))))))))) (allB_succ 28 176 (allA_of_3_0
  28 28 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 176 (allA_succ_of_accept 26 27 176
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 176 (accept_3_2 25 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 176 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 176 (accept_3_2 22 27 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 176 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 27 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 176
  (Polychromatic418967fa.accept_24_20_3_8_1_9889 20 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 176 (accept_3_2 19 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 176 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 176 (accept_3_2 16 27 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 176 (Polychromatic418967fa.accept_21_15_6_8_1_9888 15 27 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 176
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 176 (accept_3_2 13 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 176 (accept_3_2 10 27 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 176
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 176 (accept_3_2 7 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 176 (accept_3_2 4 27 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 176 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 176 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 176 (accept_3_2 1 27 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 176))))))))))))))))))))))))))) (allB_succ 26 176
  (allA_succ_of_accept 25 26 176 (accept_3_2 25 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  176 2 12 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 176 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 176 2 11 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 176 2 10 13 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 176 (accept_3_2 19 26 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 176 2 9 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  26 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 176 2 8 13 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 176
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 176 2 7 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 176 (accept_3_2 13 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  176 2 6 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 176 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 176 2 5 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 176 (Polychromatic418967fa.accept_19_9_7_5_1_9887 9 26 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 176 2 4 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 176 (accept_3_2 7 26 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 176 2 3 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 176 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 176 2 2 13 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 176
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 176 2 1 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 176 (accept_3_2 1 26 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  176)))))))))))))))))))))))))) (allB_succ 25 176 (allA_of_3_0 25 25 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 176 (allA_succ_of_accept 23 24 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 176 2 11 12 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 176 4 5 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 176 (accept_3_2 19 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  176 2 9 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 176 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 176 8 2 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 176 2 7 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 176 (accept_3_2 13 24 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 176 4 3 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 176 2 5 12 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 176
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 176 8 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 176 (accept_3_2 7 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 176
  2 3 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 176 4 1 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 176 2 1 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 176 (accept_3_2 1 24 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 176)))))))))))))))))))))))) (allB_succ 23 176 (allA_succ_of_accept 22 23 176 (accept_3_2 22
  23 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 176 (accept_3_2 19 23 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 176 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 23 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 176 (accept_3_2 16 23
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 176 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 176
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 176 (accept_3_2 13 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 176 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 176 (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 23 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 176 (accept_3_2 10 23 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 176
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 176 (accept_3_2 7 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 23 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 176 (accept_3_2 4 23 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 176 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  23 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 176 (accept_3_2 1 23 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 176))))))))))))))))))))))) (allB_succ 22 176 (allA_of_3_0 22 22
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 176 (allA_succ_of_accept 20 21 176
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 176 (accept_3_2 19 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 176 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 176 (accept_3_2 16 21 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 176 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 176
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 176 (accept_3_2 13 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 176 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 176 (accept_3_2 10 21 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 176 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 21 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 176
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 176 (accept_3_2 7 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  176 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 176 (accept_3_2 4 21 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 176 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 21 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 176 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 176 (accept_3_2 1 21 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 176))))))))))))))))))))) (allB_succ 20 176 (allA_succ_of_accept
  19 20 176 (accept_3_2 19 20 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 176 2 9 10 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 176
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 176 4 4 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 176 2 7 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 176 (accept_3_2 13 20 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 176 4 3 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 176 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 20 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 176 2 5 10 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 176
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 176 4 2 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 176 (accept_3_2 7 20 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 176
  2 3 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 176 4 1 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 176 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 176 2 1 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 176 (accept_3_2 1 20 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 176)))))))))))))))))))) (allB_succ 19 176 (allA_of_3_0 19 19 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 176 (allA_succ_of_accept 17 18 176 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 176 2 8 9 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 176
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 176 2 7 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 176 (accept_3_2 13 18 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  176 2 6 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 176 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 18 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 176 2 5 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 176 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 176 2 4 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 176 (accept_3_2 7 18 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 176 2 3 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 176 2 2 9 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 176
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 176 2 1 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 176 (accept_3_2 1 18 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  176)))))))))))))))))) (allB_succ 17 176 (allA_succ_of_accept 16 17 176 (accept_3_2 16 17 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 176
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 176 (accept_3_2 13 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 176 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 176 (accept_3_2 10 17 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 176
  (Polychromatic418967fa.accept_23_8_17_15_1_9886 8 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 176 (accept_3_2 7 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  176 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 176 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 176 (accept_3_2 4 17 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 176 (accept_3_2 1 17 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 176))))))))))))))))) (allB_succ 16 176 (allA_of_3_0 16 16 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 176 (allA_succ_of_accept 14 15 176
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 176 (accept_3_2 13 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 176 (accept_3_2 10 15 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 176 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 15 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 176
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 176 (accept_3_2 7 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  176 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 176 (accept_3_2 4 15 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 176 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 176 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  15 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 176 (accept_3_2 1 15 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 176))))))))))))))) (allB_succ 14 176 (allA_succ_of_accept 13 14
  176 (accept_3_2 13 14 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 176 2 6 7 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 176
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 176 2 5 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 176 (Polychromatic418967fa.accept_19_9_14_5_1_1890 9 14 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 176 2 4 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 176 (accept_3_2 7 14 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 176 2 3 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 176 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 176 2 2 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 176 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  14 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 176 2 1 7 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 176 (accept_3_2 1 14
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 176)))))))))))))) (allB_succ 13 176 (allA_of_3_0 13 13 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 176 (allA_succ_of_accept 11 12 176
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 176 2 5 6 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 176 (Polychromatic418967fa.accept_19_9_12_5_1_5695 9 12 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 176 4 2 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 176 (accept_3_2 7 12 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 176 2 3 6 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 176 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 12 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 176 4 1 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 176 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 176 2 1 6 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 176 (accept_3_2 1 12
  176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 176)))))))))))) (allB_succ 11 176 (allA_succ_of_accept 10 11
  176 (accept_3_2 10 11 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 176
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 176 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 176 (accept_3_2 7 11 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 176 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 176 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  11 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 176 (accept_3_2 4 11 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 176
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 11 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 176 (accept_3_2 1 11 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  176))))))))))) (allB_succ 10 176 (allA_of_3_0 10 10 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 176
  (allA_succ_of_accept 8 9 176 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 9 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 176 (accept_3_2 7 9 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 176 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 176 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 176 (accept_3_2 4 9 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 176 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 176
  (Polychromatic418967fa.accept_13_2_9_7_1_164 2 9 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 176 (accept_3_2 1 9 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 176)))))))))
  (allB_succ 8 176 (allA_succ_of_accept 7 8 176 (accept_3_2 7 8 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 176 2 3 4 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 176 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 8 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 176 4 1 2 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 176 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 176 2 1 4 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 176 (accept_3_2 1 8 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 176)))))))) (allB_succ 7 176 (allA_of_3_0 7 7 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 176 (allA_succ_of_accept 5 6 176 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 176 2 2 3 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 176
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 176 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 176 2 1 3 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 176 (accept_3_2 1 6 176 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 176))))))
  (allB_succ 5 176 (allA_succ_of_accept 4 5 176 (accept_3_2 4 5 176 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 176 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 176 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 176 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 5 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 176 (accept_3_2 1 5 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 176))))) (allB_succ 4 176 (allA_of_3_0 4 4 176 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 176 (allA_succ_of_accept 2 3 176 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 176
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 176 (accept_3_2 1 3 176 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 176))) (allB_succ 2 176 (allA_succ_of_accept 1 2 176 (accept_3_2 1 2 176
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 176)) (allB_two
  176))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


