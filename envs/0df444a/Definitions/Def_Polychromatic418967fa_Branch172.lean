-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch172
-- name    : Polychromatic418967fa_Branch172
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:31.271194+00:00
-- url     : https://prove2.me/theorems/a7974c9d-e319-49cf-9b24-454b288ec4d9
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

def Polychromatic418967fa.branch_172 : allB 172 172 :=
  allB_succ' 2 171 172 (Eq.refl Bool.true) (allA_succ_of_accept 1 171 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  171 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 172)) (allB_succ' 3 170 172
  (Eq.refl Bool.true) (allA_of_3_1 3 170 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 169 172 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 169 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 172 (accept_3_3 2 169 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 169 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 172)))) (allB_succ' 5 168 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 168 172 4 1 42 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 172 2 1 84 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 172 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 168 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 172))))) (allB_succ' 6 167 172 (Eq.refl
  Bool.true) (allA_of_3_1 6 167 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 166 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 166 172 2 3 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 172 (accept_3_3 5 166 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  172 2 2 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 166 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 172 2 1 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 166 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 166 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 172))))))) (allB_succ' 8 165 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 165 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 172 (accept_3_3 5 165 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  165 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 172
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 165 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 172 (accept_3_3 2 165 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 172)))))))) (allB_succ' 9 164 172 (Eq.refl Bool.true) (allA_of_3_1 9 164 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 163 172 (Eq.refl Bool.true) (allA_succ_of_accept 9 163 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 172 (accept_3_3 8 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 172 (accept_3_3 5 163 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 172 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 163 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 172 (accept_3_3 2 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 172 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 163 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 172)))))))))) (allB_succ' 11 162 172 (Eq.refl Bool.true) (allA_succ_of_gcd 10 162 172 2 5 81
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 172 2 4 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 172 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 162 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 172 2 3 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 172 (accept_3_3 5 162 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 172 2 2 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 162 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 172 2 1 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 172 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1
  162 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 172))))))))))) (allB_succ' 12 161
  172 (Eq.refl Bool.true) (allA_of_3_1 12 161 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 160 172
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 160 172 4 3 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 160 172 (accept_3_3 11 160 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 172 2 5 80 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 160 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 172 4 2 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 172 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 160 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 172 2 3 80 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 172 (accept_3_3 5 160 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 172 4 1 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  160 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 172 2 1 80 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 172
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 160 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 172))))))))))))) (allB_succ' 14 159 172 (Eq.refl Bool.true) (allA_succ_of_accept 13 159 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 159 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 172 (accept_3_3 11 159 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 159 172 (Polychromatic418967fa.accept_19_10_7_1_1_1685 10 159 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 172 (accept_3_3 8 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 172 (accept_3_3 5 159 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 159 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 172
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 172 (accept_3_3 2 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 172)))))))))))))) (allB_succ' 15 158 172 (Eq.refl Bool.true) (allA_of_3_1 15 158 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 157 172 (Eq.refl Bool.true) (allA_succ_of_accept 15 157 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 172 (accept_3_3 14 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 172 (accept_3_3 11 157 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 157 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 172 (accept_3_3 8 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 172 (accept_3_3 5 157 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 157 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 172 (accept_3_3 2 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 172)))))))))))))))) (allB_succ' 17 156 172 (Eq.refl Bool.true) (allA_succ_of_gcd 16 156 172
  4 4 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156
  172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 156 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 156 172 2 7 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 156 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 172 4 3 39 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 172 (accept_3_3 11 156 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 172 2 5 78 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 172
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 156 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 172 4 2 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 172 2 3 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 172 (accept_3_3 5 156 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 172 4 1 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 172 (Polychromatic418967fa.accept_19_3_4_1_1_9733 3 156 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 172 2 1 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  156 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 172))))))))))))))))) (allB_succ' 18
  155 172 (Eq.refl Bool.true) (allA_of_3_1 18 155 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 154 172
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 154 172 2 9 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 172 (accept_3_3 17 154 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 172 2 8 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 154 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 154 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 172 2 7 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 172 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 154 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 172 2 6 77 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 172
  (accept_3_3 11 154 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 172 2 5 77 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 172
  (Polychromatic418967fa.accept_19_9_2_1_1_2821 9 154 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 172 2 4 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 154 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 172 2 3 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 172 (accept_3_3 5 154 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 172 2 2 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 172 (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 154 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 172 2 1 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  154 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 172))))))))))))))))))) (allB_succ'
  20 153 172 (Eq.refl Bool.true) (allA_succ_of_accept 19 153 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 172 (accept_3_3 17 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 172 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 153 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 172 (accept_3_3 14 153 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 172 (accept_3_3 11 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 172 (accept_3_3 8 153 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 172 (accept_3_3 5 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 172 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 153 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 172 (accept_3_3 2 153 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 172)))))))))))))))))))) (allB_succ' 21 152 172
  (Eq.refl Bool.true) (allA_of_3_1 21 152 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 151 172 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 151 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 172 (accept_3_3 20 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 172
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 172 (accept_3_3 17 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 172 (accept_3_3 14 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 172 (accept_3_3 11 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 172 (accept_3_3 8 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 172 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 151 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 172 (accept_3_3 5 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 172 (accept_3_3 2 151 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 172 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 151 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 172)))))))))))))))))))))) (allB_succ' 23 150 172
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 150 172 2 11 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 172 2 10 75 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 172
  (Polychromatic418967fa.accept_23_19_12_11_1_9742 19 150 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 150 172 2 9 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 150 172 (accept_3_3 17 150 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 172 2 8 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 150 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 172 2 7 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  150 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 172 2 6 75 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 172 (accept_3_3 11
  150 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 172 2 5 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 150 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 172 2 4 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 172 2 3 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 172 (accept_3_3 5 150 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 172 2 2 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 150 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 172 2 1 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  150 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 172)))))))))))))))))))))))
  (allB_succ' 24 149 172 (Eq.refl Bool.true) (allA_of_3_1 24 149 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 148 172 (Eq.refl Bool.true) (allA_succ_of_gcd 24 148 172 4 6 37 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 172 (accept_3_3 23 148 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 172 2 11 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  148 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 172 4 5 37 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 172 2 9 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 172 (accept_3_3 17 148 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 172 4 4 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 148 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 172 2 7 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 172 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 148 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 172 4 3 37 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 172 (accept_3_3 11
  148 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 172 2 5 74 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 172
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 148 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 172 4 2 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 172 2 3 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 172 (accept_3_3 5 148 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 172 4 1 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 148 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 172 2 1 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 172 (Polychromatic418967fa.accept_13_1_5_3_1_888 1
  148 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 172)))))))))))))))))))))))))
  (allB_succ' 26 147 172 (Eq.refl Bool.true) (allA_succ_of_accept 25 147 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 172 (accept_3_3 23 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 172 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 147 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 172 (accept_3_3 20 147 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 172 (accept_3_3 17 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 172 (accept_3_3 14 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 172
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 172 (accept_3_3 11 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 172 (accept_3_3 8 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 172 (accept_3_3 5 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 172 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 172 (accept_3_3 2 147 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 172)))))))))))))))))))))))))) (allB_succ' 27 146 172
  (Eq.refl Bool.true) (allA_of_3_1 27 146 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 145 172 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 145 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 172 (accept_3_3 26 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 172 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 145 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 172
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 172 (accept_3_3 23 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 172 (accept_3_3 20 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 172 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 145 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 172 (accept_3_3 17 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 172 (accept_3_3 14 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 172
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 172 (accept_3_3 11 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 172 (accept_3_3 8 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 145 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 172 (accept_3_3 5 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 172 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 145 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 172 (accept_3_3 2 145 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 172)))))))))))))))))))))))))))) (allB_succ' 29 144
  172 (Eq.refl Bool.true) (allA_succ_of_gcd 28 144 172 4 7 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 144 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 172 2 13 72 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 172
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 25 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 172 4 6 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 172 (accept_3_3 23 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  144 172 2 11 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 144 172 (Polychromatic418967fa.accept_25_21_19_22_1_9741 21 144 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 172 4 5 36 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 172
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 172 2 9 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 172 (accept_3_3 17 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  144 172 4 4 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 144 172 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 172 2 7 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 144 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 172 4 3 36 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 172 (accept_3_3 11 144 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 172 2 5 72 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 172
  (Polychromatic418967fa.accept_19_9_11_1_1_8239 9 144 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 172 4 2 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 172 2 3 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 172 (accept_3_3 5 144 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 172 4 1 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 172 (Polychromatic418967fa.accept_19_3_11_1_1_8319 3 144 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 172 2 1 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 172 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1
  144 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 172)))))))))))))))))))))))))))))
  (allB_succ' 30 143 172 (Eq.refl Bool.true) (allA_of_3_1 30 143 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 142 172 (Eq.refl Bool.true) (allA_succ_of_gcd 30 142 172 2 15 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 142 172 (accept_3_3 29 142 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 142 172 2 14 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 142 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 172 2 13 71 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 172
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 172 2 12 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 172 (accept_3_3 23 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 172 2 11 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 142 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 172 2 10 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 172 2 9 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 172 (accept_3_3 17 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 172 2 8 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 172 2 7 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 142 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 172 2 6 71 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 172 (accept_3_3 11 142 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 172 2 5 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 172
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 172 2 4 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 172 2 3 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 172 (accept_3_3 5 142 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 172 2 2 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 142 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 172 2 1 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  142 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 172)))))))))))))))))))))))))))))))
  (allB_succ' 32 141 172 (Eq.refl Bool.true) (allA_succ_of_accept 31 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 172 (accept_3_3 29 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 172 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 172 (accept_3_3 26 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 172 (accept_3_3 23 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 172 (accept_3_3 20 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 172 (accept_3_3 17 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 172 (accept_3_3 14 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 172 (accept_3_3 11 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 172 (accept_3_3 8 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 172
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 172 (accept_3_3 5 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 172 (accept_3_3 2 141 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 172)))))))))))))))))))))))))))))))) (allB_succ' 33
  140 172 (Eq.refl Bool.true) (allA_of_3_1 33 140 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 139 172
  (Eq.refl Bool.true) (allA_succ_of_accept 33 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 172 (accept_3_3 32 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 172 (accept_3_3 29 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 172 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 172 (accept_3_3 26 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 172 (accept_3_3 23 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 172 (accept_3_3 20 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 172
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 172 (accept_3_3 17 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 172 (accept_3_3 14 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 172 (Polychromatic418967fa.accept_20_13_19_12_1_5143 13 139 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 172 (accept_3_3 11 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 172 (accept_3_3 8 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 172 (accept_3_3 5 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 172 (Polychromatic418967fa.accept_16_4_11_12_1_1775 4 139 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 172 (accept_3_3 2 139 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 139 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 172)))))))))))))))))))))))))))))))))) (allB_succ' 35
  138 172 (Eq.refl Bool.true) (allA_succ_of_gcd 34 138 172 2 17 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 172 2 16 69 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 172 2 15 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 172 (accept_3_3 29 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 172 2 14 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 172 2 13 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 172 2 12 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 172 (accept_3_3 23 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 172 2 11 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 172 2 10 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 172
  (Polychromatic418967fa.accept_15_4_3_7_1_713 19 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 172 2 9 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 172 (accept_3_3 17 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 172 2 8 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 172 2 7 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 138 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 172 2 6 69 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 172 (accept_3_3 11 138 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 172 2 5 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 172 2 4 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 172 2 3 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 172 (accept_3_3 5 138 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 172 2 2 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 138 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 172 2 1 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  138 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  172))))))))))))))))))))))))))))))))))) (allB_succ' 36 137 172 (Eq.refl Bool.true) (allA_of_3_1 36 137 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 136 172 (Eq.refl Bool.true) (allA_succ_of_gcd 36 136 172 4 9 34 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 172
  (accept_3_3 35 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 172 2 17 68 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 172
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 172 4 8 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 136 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 136 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 172 2 15 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 172 (accept_3_3 29 136 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 172 4 7 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 136 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 172 2 13 68 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 172
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 172 4 6 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 136 172 (accept_3_3 23 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  136 172 2 11 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 136 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 136 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 172 4 5 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 172 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  19 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 172 2 9 68 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 172
  (accept_3_3 17 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 172 4 4 34 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 136 172 2 7 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 136 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 136 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 172 4 3 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 172 (accept_3_3 11 136 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 172 2 5 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 172 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 136 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 172 4 2 34 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 172
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 172 2 3 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 172 (accept_3_3 5 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  172 4 1 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 172 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 136 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 172 2 1 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 136 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 172))))))))))))))))))))))))))))))))))))) (allB_succ' 38 135 172
  (Eq.refl Bool.true) (allA_succ_of_accept 37 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 172
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 172 (accept_3_3 35 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 172 (accept_3_3 32 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 172 (accept_3_3 29 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 172 (accept_3_3 26 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 172
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 172 (accept_3_3 23 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 172 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 172 (accept_3_3 20 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 172 (accept_3_3 17 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 172 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 172 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 172 (accept_3_3 14 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 172 (accept_3_3 11 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 172 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 172 (accept_3_3 8 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 172 (accept_3_3 5 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 172 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 135 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 172 (accept_3_3 2 135 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 172))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 134 172 (Eq.refl Bool.true) (allA_of_3_1 39 134 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 133 172 (Eq.refl Bool.true) (allA_succ_of_accept 39 133 172 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 172 (accept_3_3 38
  133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 172
  (Polychromatic418967fa.accept_17_3_14_2_1_646 37 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 133 172 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 133 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 172 (accept_3_3 35 133 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 133 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 172 (accept_3_3 32 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 172 (accept_3_3 29 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 172 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 172 (accept_3_3 26 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 172 (accept_3_3 23 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 172 (accept_3_3 20 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 172 (Polychromatic418967fa.accept_20_19_13_12_1_2476 19 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 172 (Polychromatic418967fa.accept_21_18_7_4_1_8131 18 133 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 172 (accept_3_3 17 133 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 172
  (Polychromatic418967fa.accept_17_16_14_2_1_5841 16 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 172 (accept_3_3 14 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 172 (accept_3_3 11 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 172 (accept_3_3 8 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 172 (Polychromatic418967fa.accept_16_7_5_12_1_4824 7 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 172 (accept_3_3 5 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 172 (accept_3_3 2 133 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 172))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 132 172 (Eq.refl Bool.true) (allA_succ_of_gcd 40 132 172 4 10 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 172 2 19 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 132 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 172 4 9 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 172 (accept_3_3 35 132 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 172 2 17 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 172 4 8 33 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 172 2 15 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 172 (accept_3_3 29 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 172 4 7 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 172 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 132 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 172 2 13 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 25
  132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 172 4 6 33 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 172 (accept_3_3 23
  132 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 172 2 11 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 172 4 5 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 172 2 9 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 172 (accept_3_3 17 132 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 172 4 4 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 172 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 132
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 172 2 7 66 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 172 4 3 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 172 (accept_3_3 11 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  132 172 2 5 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 132 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 132 172 4 2 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 132 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 172 2 3 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 172 (accept_3_3 5 132 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 172 4 1 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 172 2 1 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 172
  (Polychromatic418967fa.accept_13_1_2_3_1_911 1 132 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 172))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 131 172 (Eq.refl Bool.true) (allA_of_3_1 42
  131 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 130 172 (Eq.refl Bool.true) (allA_succ_of_gcd 42 130
  172 2 21 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  130 172 (accept_3_3 41 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 172 2 20 65 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 130 172 2 19 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 130 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 130 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 172 2 18 65 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 172 (accept_3_3 35 130 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 172 2 17 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 130 172 2 16 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 130 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 172 2 15 65 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 172 (accept_3_3 29 130 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 172 2 14 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 172
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 172 2 13 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 130 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 130 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 130 172 2 12 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 172 (accept_3_3 23 130 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 172 2 11 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 172 2 10 65 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 172 2 9 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 172 (accept_3_3 17 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 172 2 8 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 172 2 7 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 172 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 130 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 172 2 6 65 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 172 (accept_3_3 11 130 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 172 2 5 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 172
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 172 2 4 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 172 2 3 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 172 (accept_3_3 5 130 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 172 2 2 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 130 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 172 2 1 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  130 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  172))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 129 172 (Eq.refl Bool.true) (allA_succ_of_gcd 43 129 172
  43 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 42 129
  172 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 172 (accept_3_3 41 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 129 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 172 (Polychromatic418967fa.accept_20_19_9_12_1_9740 39 129
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 172 (accept_3_3 38 129
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 172 (accept_3_3 35 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 172 (accept_3_3 32 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 172 (accept_3_3 29 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 172 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 172 (accept_3_3 26 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 172 (accept_3_3 23 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 172 (accept_3_3 20 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 172 (accept_3_3 17 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 172 (accept_3_3 14 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 172
  (Polychromatic418967fa.accept_17_12_10_2_1_5835 12 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 172 (accept_3_3 11 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 172 (Polychromatic418967fa.accept_31_10_5_17_1_9739 10 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 172 (Polychromatic418967fa.accept_13_9_12_3_1_907
  9 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 172 (accept_3_3 8
  129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 129 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 172 (accept_3_3 5 129 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 129 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 129 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 172 (Polychromatic418967fa.accept_20_3_9_12_1_6671
  3 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 172 (accept_3_3 2
  129 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 172)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 128 172 (Eq.refl Bool.true) (allA_of_3_1
  45 128 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 127 172 (Eq.refl Bool.true) (allA_succ_of_accept 45
  127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 127 172 (accept_3_3 44 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 127 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 127 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 172 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 127
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 172 (accept_3_3 41 127
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 40 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 172 (accept_3_3 38 127 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 127 172 (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 127 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 172
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 127 172 (accept_3_3 35 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 127 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 127 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 172 (accept_3_3 32 127 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 172 (Polychromatic418967fa.accept_7_3_1_4_1_121
  31 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 172
  (Polychromatic418967fa.accept_25_5_2_22_1_9738 30 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 172 (accept_3_3 29 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 172 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 172 (accept_3_3 26 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 172 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 127 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 172 (accept_3_3 23 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 172 (accept_3_3 20 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 172
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 127 172 (accept_3_3 17 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 172 (Polychromatic418967fa.accept_17_16_8_2_1_5890 16 127 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 172 (accept_3_3 14 127 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 172
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 172 (accept_3_3 11 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 172 (accept_3_3 8 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 172 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 172 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 172 (accept_3_3 5 127 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 127 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 172 (accept_3_3 2 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 127 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 172)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 126 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 126 172 2 23 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 172 2 22 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 172
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 172 2 21 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 172 (accept_3_3 41 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 172 2 20 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 172 2 19 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 172
  (Polychromatic418967fa.accept_19_18_12_1_1_9737 37 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 172 2 18 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 172 (accept_3_3 35 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 172 2 17 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 172 2 16 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 172
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 172 2 15 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 172 (accept_3_3 29 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 172 2 14 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 172 2 13 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 172
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 172 2 12 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 172 (accept_3_3 23 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 172 2 11 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 172 2 10 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 172
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 172 2 9 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 172 (accept_3_3 17 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  126 172 2 8 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 126 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 126 172 2 7 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 172 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 126 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 172 2 6 63 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 172 (accept_3_3 11 126 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 172 2 5 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 172
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 172 2 4 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 172 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 126 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 172 2 3 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 172 (accept_3_3 5 126 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 172 2 2 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 126 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 172 2 1 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  126 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  172))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 125 172 (Eq.refl Bool.true) (allA_of_3_1 48 125 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 124 172 (Eq.refl Bool.true) (allA_succ_of_gcd 48 124 172 4 12
  31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 124 172
  (accept_3_3 47 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 124 172 2 23 62 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 124 172
  (Polychromatic418967fa.accept_19_7_10_1_1_5382 45 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 124 172 4 11 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 124 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 124 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 124 172 2 21 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 124 172 (accept_3_3 41 124 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 124 172 4 10 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 124 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 39
  124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 172 2 19 62 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 172 4 9 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 172 (accept_3_3 35 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 172 2 17 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 124 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 172 4 8 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 172 2 15 62 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 172 (accept_3_3 29
  124 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 172 4 7 31 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 172 2 13 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 172 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 124 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 172 4 6 31 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 172 (accept_3_3 23 124 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 172 2 11 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 172 4 5 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 172 (Polychromatic418967fa.accept_18_1_16_10_1_2065 19 124 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 172 2 9 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 172 (accept_3_3 17 124 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 172 4 4 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 172 2 7 62 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 172 4 3 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 172 (accept_3_3 11 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 172 2 5 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 124 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 124 172 4 2 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 124 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 172 2 3 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 172 (accept_3_3 5 124 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 172 4 1 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 124 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 124 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 172 2 1 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 172))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 123 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 123 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 123 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 172 (accept_3_3 47 123 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 172
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 46 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 123 172 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 123 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 172 (accept_3_3 44 123 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  42 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 172 (accept_3_3 41
  123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 123 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 172 (accept_3_3 38 123 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 172
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 172 (accept_3_3 35 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 172 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 172 (accept_3_3 32 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 172 (accept_3_3 29 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 172 (Polychromatic418967fa.accept_21_7_18_4_1_5024 28 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 172 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 172 (accept_3_3 26 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 172
  (Polychromatic418967fa.accept_16_8_11_12_1_962 24 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 172 (accept_3_3 23 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 172 (accept_3_3 20 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 172 (accept_3_3 17 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 172 (accept_3_3 14 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 172 (accept_3_3 11 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 172 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 172 (accept_3_3 8 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 172 (accept_3_3 5 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 123 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 172 (accept_3_3 2 123 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  172)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 122 172 (Eq.refl Bool.true) (allA_of_3_1 51 122
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 121 172 (Eq.refl Bool.true) (allA_succ_of_accept 51 121
  172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 172 (accept_3_3 50 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 172 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 172 (accept_3_3 47 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 172 (accept_3_3 44 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 172 (accept_3_3 41 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 172 (accept_3_3 38 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 172 (accept_3_3 35 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 121 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 172 (accept_3_3 32 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 172 (Polychromatic418967fa.accept_19_12_7_1_1_5400 31 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 172 (accept_3_3 29 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 172 (Polychromatic418967fa.accept_21_7_16_4_1_9713 28 121 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 172 (accept_3_3 26 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 172 (accept_3_3 23 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 172 (accept_3_3 20 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 172 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 172 (accept_3_3 17 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 172 (accept_3_3 14 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 172 (accept_3_3 11 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 172 (accept_3_3 8 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 172 (accept_3_3 5 121 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 172 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 121 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 172 (accept_3_3 2 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 172 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 121 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 172)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 120 172 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 120 172 4 13 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 120 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 120 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 172 2 25 60 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 172 4 12 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 172 (accept_3_3 47 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 172 2 23 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 172 4 11 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 172 2 21 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 172 (accept_3_3 41 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 172 4 10 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 172 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 120 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 172 2 19 60 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 172
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 37 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 172 4 9 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 172 (accept_3_3 35 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  120 172 2 17 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 120 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 172 4 8 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 172 2 15 60 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 172 (accept_3_3 29
  120 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 172 4 7 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 172
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 120 172 2 13 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 120 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 120 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 172 4 6 30 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 172 (accept_3_3 23 120 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 172 2 11 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 172
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 172 4 5 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 172 2 9 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 172 (accept_3_3 17 120 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 172 4 4 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 172 2 7 60 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 172 4 3 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 120 172 (accept_3_3 11 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  120 172 2 5 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 120 172 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 120 172 4 2 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 120 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 172 2 3 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 172 (accept_3_3 5 120 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 172 4 1 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 120 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 172 2 1 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 172
  (Polychromatic418967fa.accept_16_1_8_12_1_405 1 120 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 172))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 119 172 (Eq.refl Bool.true)
  (allA_of_3_1 54 119 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 118 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 118 172 2 27 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 172 (accept_3_3 53 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 172 2 26 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 118 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 172 2 25 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 172 2 24 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 172 (accept_3_3 47 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 172 2 23 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 118 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 172 2 22 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 172 2 21 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 172 (accept_3_3 41 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 172 2 20 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 172 (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 118 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 172 2 19 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 172 2 18 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 172 (accept_3_3 35 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 172 2 17 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 118 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 172 2 16 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 172 2 15 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 172 (accept_3_3 29 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 172 2 14 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 172 (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 118 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 172 2 13 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 172
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 172 2 12 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 172 (accept_3_3 23 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 172 2 11 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 172 (Polychromatic418967fa.accept_15_6_13_7_1_222 21 118 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 172 2 10 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 172 2 9 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 172 (accept_3_3 17 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 172 2 8 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 172 2 7 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 118 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 172 2 6 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 172 (accept_3_3 11 118 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 172 2 5 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 172 2 4 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 118 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 172 2 3 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 172 (accept_3_3 5 118 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 172 2 2 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 172 2 1 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  118 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 117 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 117 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 117
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 172 (accept_3_3 53 117
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 172
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 117 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 172 (accept_3_3 50 117 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 172 (Polychromatic418967fa.accept_7_6_5_4_1_297
  48 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 172 (accept_3_3 47
  117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 172
  (Polychromatic418967fa.accept_20_6_17_12_1_8210 46 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 172 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 172 (accept_3_3 44 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 117 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 172 (accept_3_3 41 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 172 (Polychromatic418967fa.accept_15_10_12_7_1_1358 40 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 172 (accept_3_3 38 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 172 (accept_3_3 35 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 172 (accept_3_3 32 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 172 (accept_3_3 29 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 172 (Polychromatic418967fa.accept_21_7_12_4_1_6493 28 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 172 (accept_3_3 26 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 172 (accept_3_3 23 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 172 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 172 (accept_3_3 20 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 172 (accept_3_3 17 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 172 (accept_3_3 14 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 172
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 12 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 172 (accept_3_3 11 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 172 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 117 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 172 (accept_3_3 8 117
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 172 (accept_3_3 5 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 117 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 172 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 172 (accept_3_3 2 117 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 116 172 (Eq.refl Bool.true) (allA_of_3_1 57
  116 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 115 172 (Eq.refl Bool.true) (allA_succ_of_accept 57
  115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 115 172 (accept_3_3 56 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 115 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 115
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 172 (accept_3_3 53 115
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 172
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 172 (accept_3_3 50 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 115 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 172 (Polychromatic418967fa.accept_7_6_3_4_1_294
  48 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 172 (accept_3_3 47
  115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 172
  (Polychromatic418967fa.accept_12_10_7_4_1_820 46 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 172 (accept_3_3 44 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 115 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 172 (Polychromatic418967fa.accept_9_6_7_1_1_145
  42 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 172 (accept_3_3 41
  115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 40 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 172 (accept_3_3 38 115 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 115 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 172 (accept_3_3 35 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 172 (accept_3_3 32 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 115 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 172 (accept_3_3 29 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 172 (accept_3_3 26 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 172 (Polychromatic418967fa.accept_16_9_3_12_1_1802 25 115 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 172 (accept_3_3 23 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 172 (accept_3_3 20 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 172 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 115 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 172 (accept_3_3 17 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 172 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 172 (accept_3_3 14 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 115 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 172 (accept_3_3 11 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 172 (accept_3_3 8 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 172 (accept_3_3 5 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 172 (accept_3_3 2 115 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 114 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 114 172 2 29 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 172 2 28 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 172 2 27 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 172 (accept_3_3 53 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 172 2 26 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 172 2 25 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 172 2 24 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 172 (accept_3_3 47 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 172 2 23 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 172 2 22 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 172 2 21 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 172 (accept_3_3 41 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 172 2 20 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 172 2 19 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 172
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 172 2 18 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 172 (accept_3_3 35 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 172 2 17 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 172 2 16 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 172 2 15 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 172 (accept_3_3 29 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 172 2 14 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 172 2 13 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 172 2 12 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 172 (accept_3_3 23 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 172 2 11 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 172 2 10 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 172 2 9 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 172 (accept_3_3 17 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 172 2 8 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 172 2 7 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 114 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 172 2 6 57 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 172 (accept_3_3 11 114 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 172 2 5 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 172 2 4 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 172 2 3 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 172 (accept_3_3 5 114 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 172 2 2 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 172 2 1 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 172 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1
  114 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 113 172 (Eq.refl Bool.true) (allA_of_3_1
  60 113 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 112 172 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  112 172 4 15 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 112 172 (accept_3_3 59 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  112 172 2 29 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 112 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 112 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 172 4 14 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 172 (Polychromatic418967fa.accept_21_13_7_4_1_4991
  55 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 172 2 27 56 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 172
  (accept_3_3 53 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 172 4 13 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 112 172 2 25 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 112 172 (Polychromatic418967fa.accept_17_15_10_2_1_2309 49 112 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 112 172 4 12 28 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 172 (accept_3_3 47 112 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 172 2 23 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 172
  (Polychromatic418967fa.accept_21_3_7_4_1_9736 45 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 172 4 11 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 172 2 21 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 172 (accept_3_3 41 112 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 172 4 10 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 39
  112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 172 2 19 56 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 172
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 172 4 9 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 112 172 (accept_3_3 35 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  112 172 2 17 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 112 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 112 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 172 4 8 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  31 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 172 2 15 56 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 172
  (accept_3_3 29 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 172 4 7 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 172
  (Polychromatic418967fa.accept_21_6_7_4_1_4993 27 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 112 172 2 13 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 112 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 172 4 6 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 172 (accept_3_3 23 112 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 172 2 11 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 172 4 5 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 172
  (Polychromatic418967fa.accept_21_19_7_4_1_4994 19 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 172 2 9 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 172 (accept_3_3 17 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 172 4 4 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 172 2 7 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 172 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 112 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 172 4 3 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 172 (accept_3_3 11
  112 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 172 2 5 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 172
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 172 4 2 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 172 2 3 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 172 (accept_3_3 5 112 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 172 4 1 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 112 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 172 2 1 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 172 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1
  112 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 111 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 111 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 111 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 172 (accept_3_3 59 111 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 58
  111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 172
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 172 (accept_3_3 56 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 172 (accept_3_3 53 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 172 (accept_3_3 50 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 172 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 172 (accept_3_3 47 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 111
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 172 (accept_3_3 44 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 172 (accept_3_3 41 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 172
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 172 (accept_3_3 38 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 172 (accept_3_3 35 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 111 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 172 (accept_3_3 32 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 172 (accept_3_3 29 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 172 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 172
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 172 (accept_3_3 26 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 172 (accept_3_3 23 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 172
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 172 (accept_3_3 20 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 172 (accept_3_3 17 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 172 (accept_3_3 14 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 172 (accept_3_3 11 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 172 (accept_3_3 8 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 172 (accept_3_3 5 111 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 111 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 172 (accept_3_3 2 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 110 172
  (Eq.refl Bool.true) (allA_of_3_1 63 110 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 109 172 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 172 (accept_3_3 62 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 172
  (Polychromatic418967fa.accept_13_8_5_3_1_427 60 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 172 (accept_3_3 59 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 172 (Polychromatic418967fa.accept_11_3_10_7_1_129 58 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 172 (accept_3_3 56 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 172 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 109 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 172
  (Polychromatic418967fa.accept_13_2_5_3_1_406 54 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 172 (accept_3_3 53 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 172 (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 172 (accept_3_3 50 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 172
  (Polychromatic418967fa.accept_13_9_5_3_1_428 48 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 172 (accept_3_3 47 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 172 (accept_3_3 44 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 172 (Polychromatic418967fa.accept_14_1_11_4_1_3430 43 109 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 172
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 42 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 172 (accept_3_3 41 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 172 (Polychromatic418967fa.accept_13_1_5_3_1_888 40 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 172 (accept_3_3 38 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 172
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 172 (accept_3_3 35 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 172 (accept_3_3 32 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 172
  (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 172 (accept_3_3 29 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 172 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 172 (accept_3_3 26 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 172
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 172 (accept_3_3 23 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 172 (accept_3_3 20 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 172 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 172
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 172 (accept_3_3 17 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 172 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 172 (accept_3_3 14 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 172 (Polychromatic418967fa.accept_17_13_7_2_1_4562 13 109 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 172
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 12 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 172 (accept_3_3 11 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 172 (accept_3_3 8 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 172
  (Polychromatic418967fa.accept_13_6_5_3_1_426 6 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 172 (accept_3_3 5 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 172 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 109 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 172 (accept_3_3 2 109 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 109 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 108 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 108 172 4 16 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 172 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 108 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 172 2 31 54 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 172
  (Polychromatic418967fa.accept_22_17_20_18_1_1899 61 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 172 4 15 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 172 (accept_3_3 59 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 172 2 29 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 172 4 14 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 172 2 27 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 172 (accept_3_3 53 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 172 4 13 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 172 (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 108 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 172 2 25 54 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 172
  (Polychromatic418967fa.accept_11_5_9_7_1_411 49 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 172 4 12 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 172 (accept_3_3 47 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 172 2 23 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 108 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 172 4 11 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 172 2 21 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 172 (accept_3_3 41 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 172 4 10 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 172 (Polychromatic418967fa.accept_21_18_3_4_1_5013 39 108 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 172 2 19 54 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 172
  (Polychromatic418967fa.accept_19_18_13_1_1_9735 37 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 172 4 9 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 172 (accept_3_3 35 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 172 2 17 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 172 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 108 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 172 4 8 27 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 172
  (Polychromatic418967fa.accept_19_12_13_1_1_2779 31 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 172 2 15 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 172 (accept_3_3 29 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 172 4 7 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 172 2 13 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 172 (Polychromatic418967fa.accept_10_5_8_2_1_517
  25 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 172 4 6 27 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 172
  (accept_3_3 23 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 172 2 11 54 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 172
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 172 4 5 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 172 (Polychromatic418967fa.accept_15_4_3_7_1_713 19 108 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 172 2 9 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 172 (accept_3_3 17 108 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 172 4 4 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 172 2 7 54 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 172 4 3 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 172 (accept_3_3 11 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  108 172 2 5 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 108 172 (Polychromatic418967fa.accept_22_9_20_18_1_8035 9 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 108 172 4 2 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 108 172 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 108 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 172 2 3 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 172 (accept_3_3 5 108 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 172 4 1 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 172 (Polychromatic418967fa.accept_25_3_8_22_1_9734 3 108 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 172 2 1 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 107 172 (Eq.refl
  Bool.true) (allA_of_3_1 66 107 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 106 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 106 172 2 33 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 172 (accept_3_3 65 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 172 2 32 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 172 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 106 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 172 2 31 53 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 172 2 30 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 172 (accept_3_3 59 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 172 2 29 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 172 2 28 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 172 2 27 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 172 (accept_3_3 53 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 172 2 26 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 172 2 25 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 172 2 24 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 172 (accept_3_3 47 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 172 2 23 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 172 2 22 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 172 2 21 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 172 (accept_3_3 41 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 172 2 20 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 172 2 19 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 172 2 18 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 172 (accept_3_3 35 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 172 2 17 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 172 2 16 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 172 2 15 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 172 (accept_3_3 29 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 172 2 14 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 172 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 172 2 13 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 172 2 12 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 172 (accept_3_3 23 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 172 2 11 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 172 2 10 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 172 2 9 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 172 (accept_3_3 17 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 172 2 8 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 172 2 7 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 106 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 172 2 6 53 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 172 (accept_3_3 11 106 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 172 2 5 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 172
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 172 2 4 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 172 2 3 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 172 (accept_3_3 5 106 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 172 2 2 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 172 2 1 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  106 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 105 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 105 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 172 (accept_3_3 65 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 172
  (Polychromatic418967fa.accept_19_7_10_1_1_5382 64 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 105 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 172 (accept_3_3 62 105 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 172
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 60 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 172 (accept_3_3 59 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 105 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 172 (accept_3_3 56 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 172 (accept_3_3 53 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 172 (Polychromatic418967fa.accept_16_3_9_12_1_4831 51 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 172 (accept_3_3 50 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 172 (accept_3_3 47 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 172 (Polychromatic418967fa.accept_13_7_1_3_1_1523 46 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 172 (accept_3_3 44 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 172 (accept_3_3 41 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 172 (accept_3_3 38 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 172
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 172 (accept_3_3 35 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 172 (accept_3_3 32 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 172 (accept_3_3 29 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 172 (accept_3_3 26 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 172
  (Polychromatic418967fa.accept_13_11_1_3_1_910 24 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 172 (accept_3_3 23 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 172 (accept_3_3 20 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 172 (accept_3_3 17 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 172 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 172 (accept_3_3 14 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 172 (accept_3_3 11 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 172 (Polychromatic418967fa.accept_18_9_15_10_1_395 9 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 172 (accept_3_3 8 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 172 (accept_3_3 5 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 105 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 172 (accept_3_3 2 105 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 104 172 (Eq.refl Bool.true)
  (allA_of_3_1 69 104 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 103 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 172 (accept_3_3 68 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 103 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 172 (accept_3_3 65
  103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 64 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 172 (accept_3_3 62 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 103 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 172 (Polychromatic418967fa.accept_9_6_4_1_1_390
  60 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 172 (accept_3_3 59
  103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 58 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 172 (accept_3_3 56 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 103 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 172 (Polychromatic418967fa.accept_13_2_12_3_1_415
  54 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 172 (accept_3_3 53
  103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 52 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 172 (accept_3_3 50 103 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 103 172 (Polychromatic418967fa.accept_19_11_8_1_1_801 49 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 172 (accept_3_3 47 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 172 (accept_3_3 44 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 172 (accept_3_3 41 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 172 (Polychromatic418967fa.accept_16_8_7_12_1_7207 40 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 172 (accept_3_3 38 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 172 (accept_3_3 35 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 172 (accept_3_3 32 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 172 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 172 (accept_3_3 29 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 172 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 172 (accept_3_3 26 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 172 (accept_3_3 23 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 172 (accept_3_3 20 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 172
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 172 (accept_3_3 17 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 172 (accept_3_3 14 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 172 (accept_3_3 11 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 172 (accept_3_3 8 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 172 (accept_3_3 5 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 172 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 103 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 172 (accept_3_3 2 103 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 102 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 102 172 2 35 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 172 2 34 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 172 2 33 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 172 (accept_3_3 65 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 172 2 32 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 172 2 31 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 172 2 30 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 172 (accept_3_3 59 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 172 2 29 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 172 2 28 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 172
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 102 172 2 27 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 102 172 (accept_3_3 53 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 172 2 26 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 172 2 25 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 172 2 24 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 172 (accept_3_3 47 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 172 2 23 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 172 2 22 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 172 2 21 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 172 (accept_3_3 41 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 172 2 20 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 172 2 19 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 172
  (Polychromatic418967fa.accept_11_4_3_7_1_828 37 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 172 2 18 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 172 (accept_3_3 35 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 172 2 17 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 172 2 16 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 172 2 15 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 172 (accept_3_3 29 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 172 2 14 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 172 2 13 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 172 2 12 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 172 (accept_3_3 23 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 172 2 11 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 102 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 172 2 10 51 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 172
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 172 2 9 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 172 (accept_3_3 17 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 172 2 8 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 172 2 7 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 102 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 172 2 6 51 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 172 (accept_3_3 11 102 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 172 2 5 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 172 2 4 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 172 2 3 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 172 (accept_3_3 5 102 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 172 2 2 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 172 2 1 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 172 (Polychromatic418967fa.accept_13_1_11_3_1_901 1
  102 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 101 172 (Eq.refl Bool.true)
  (allA_of_3_1 72 101 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 100 172 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 100 172 4 18 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 172 (accept_3_3 71 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 172 2 35 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 172 4 17 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 172
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 172 2 33 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 172 (accept_3_3 65 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 172 4 16 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 172 (Polychromatic418967fa.accept_15_3_10_7_1_2196 63 100 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 172 2 31 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 172 4 15 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 172 (accept_3_3 59 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 172 2 29 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 172 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 172 4 14 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 172 2 27 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 172 (accept_3_3 53 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 172 4 13 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 172 (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 100 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 172 2 25 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 172
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 172 4 12 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 172 (accept_3_3 47 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 172 2 23 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 172 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 172 4 11 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 172
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 43 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 100 172 2 21 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 100 172 (accept_3_3 41 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 172 4 10 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 172 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 100 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 172 2 19 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 172
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 172 4 9 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 100 172 (accept_3_3 35 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  100 172 2 17 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 100 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 100 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 172 4 8 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 172 (Polychromatic418967fa.accept_13_5_9_3_1_870
  31 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 172 2 15 50 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 172
  (accept_3_3 29 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 172 4 7 25 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 100 172 2 13 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 100 172 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 100 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 172 4 6 25 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 172 (accept_3_3 23 100 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 172 2 11 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 172
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 172 4 5 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 172 2 9 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 172 (accept_3_3 17 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 172 4 4 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 172 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 100
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 172 2 7 50 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 172 4 3 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 100 172 (accept_3_3 11 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 172 2 5 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 172 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 100 172 4 2 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 100 172 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 172 2 3 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 172 (accept_3_3 5 100 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 172 4 1 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 172 (Polychromatic418967fa.accept_15_3_10_7_1_2196 3 100 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 172 2 1 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 172
  (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 100 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 99 172
  (Eq.refl Bool.true) (allA_succ_of_accept 73 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 172
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 99 172 (accept_3_3 71 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  99 172 (Polychromatic418967fa.accept_13_5_8_3_1_1535 70 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 172 (Polychromatic418967fa.accept_18_15_9_10_1_1082 69 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 172 (accept_3_3 68 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 99 172 (accept_3_3 65 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  99 172 (Polychromatic418967fa.accept_19_7_4_1_1_5399 64 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 99 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 172 (accept_3_3 62 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 172
  (Polychromatic418967fa.accept_19_3_4_1_1_9733 60 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 99 172 (accept_3_3 59 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  99 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 58 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 172 (accept_3_3 56 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 99 172 (accept_3_3 53 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  99 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 99 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 172 (accept_3_3 50 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 172
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 172 (accept_3_3 47 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 172 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 172 (accept_3_3 44 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 172 (accept_3_3 41 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 172 (accept_3_3 38 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 172
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 172 (accept_3_3 35 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 172 (Polychromatic418967fa.accept_19_15_4_1_1_4060 34 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 172 (accept_3_3 32 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 172 (accept_3_3 29 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 172 (accept_3_3 26 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 172 (accept_3_3 23 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 172 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 172 (accept_3_3 20 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 172 (accept_3_3 17 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 172 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 172 (accept_3_3 14 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 172 (accept_3_3 11 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 172 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 172 (accept_3_3 8 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 172 (accept_3_3 5 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  172 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 99 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 172 (accept_3_3 2 99 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 98 172 (Eq.refl
  Bool.true) (allA_of_3_1 75 98 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 97 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 97 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 172 (accept_3_3 74 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 172 (accept_3_3 71 97
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 172
  (Polychromatic418967fa.accept_12_10_1_4_1_392 70 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 97 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 172 (accept_3_3 68 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 97 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 66
  97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 172 (accept_3_3 65 97
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 64 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 97 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 172 (accept_3_3 62 97 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 97 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 60
  97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 172 (accept_3_3 59 97
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 172 (Polychromatic418967fa.accept_7_2_6_4_1_29
  58 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 172 (accept_3_3 56 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 172 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 172 (accept_3_3 53 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 172 (accept_3_3 50 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 172 (accept_3_3 47 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 172 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 172 (accept_3_3 44 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 172 (Polychromatic418967fa.accept_16_11_1_12_1_1795 43 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 172 (accept_3_3 41 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 172 (accept_3_3 38 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 172 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 172 (accept_3_3 35 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 172 (accept_3_3 32 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 172 (accept_3_3 29 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 172 (Polychromatic418967fa.accept_19_9_2_1_1_2821 28 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 172 (accept_3_3 26 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 172 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 172 (accept_3_3 23 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 172 (accept_3_3 20 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 172 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 172 (accept_3_3 17 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 172 (accept_3_3 14 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 172 (accept_3_3 11 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 172 (accept_3_3 8 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  172 (Polychromatic418967fa.accept_17_7_12_2_1_7105 7 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 172 (accept_3_3 5 97 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 97 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 172 (accept_3_3 2 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  172 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 97 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 97 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 96 172 (Eq.refl Bool.true) (allA_succ_of_gcd 76 96 172 4 19 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 172 2 37 48 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 172
  (Polychromatic418967fa.accept_13_8_5_3_1_427 73 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 172 4 18 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 172 (accept_3_3 71 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96
  172 2 35 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  96 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 96 172 4 17 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 96 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 96 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 172 2 33 48 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 172 (accept_3_3 65 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 172 4 16 24 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 172
  (Polychromatic418967fa.accept_13_11_5_3_1_889 63 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 172 2 31 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 96 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 172 4 15 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 172 (accept_3_3 59 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 172 2 29 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 172 4 14 24 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 172 2 27 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 172 (accept_3_3 53 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96
  172 4 13 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  96 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 96 172 2 25 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 96 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 172 4 12 24 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 172 (accept_3_3 47 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 172 2 23 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 172
  (Polychromatic418967fa.accept_13_6_5_3_1_426 45 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 172 4 11 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 172 2 21 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 172 (accept_3_3 41 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 172 4 10 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 172 2 19 48 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 172 4 9 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 172 (accept_3_3 35 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  172 2 17 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  96 172 (Polychromatic418967fa.accept_18_15_6_10_1_5590 33 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 172 4 8 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 172 2 15 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 172 (accept_3_3 29 96 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 172 4 7 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 172 2 13 48 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 172 4 6 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 172 (accept_3_3 23 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  172 2 11 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 172 4 5 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 172 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 172 2 9 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 172 (accept_3_3 17 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 172 4 4 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 96 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 172 2 7 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 172 4 3 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 172 (accept_3_3 11 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  172 2 5 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 172 4 2 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 172 2 3 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 172 (accept_3_3 5 96 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 172 4 1 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 172 2 1 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 95 172
  (Eq.refl Bool.true) (allA_of_3_1 78 95 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 94 172 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 94 172 2 39 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 172 (accept_3_3 77 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 172 2 38 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 94 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 94 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 172 2 37 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 172 (Polychromatic418967fa.accept_12_1_10_4_1_380
  73 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 94 172 2 36 47 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 94 172 (accept_3_3 71
  94 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94 172 2 35 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 94 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 94 172 2 34 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 94 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 67 94 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 94 172 2 33 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 94 172 (accept_3_3 65 94 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94 172 2 32 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 94 172 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 172 2 31 47 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 172 2 30 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 94 172 (accept_3_3 59 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94
  172 2 29 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  94 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 94 172 2 28 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 94 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 94 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 172 2 27 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 172 (accept_3_3 53 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 172 2 26 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 94 172 2 25 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 94 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 172 2 24 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 172 (accept_3_3 47 94 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 172 2 23 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 172 2 22 47 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 172 2 21 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 94 172 (accept_3_3 41 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94
  172 2 20 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  94 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 94 172 2 19 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 94 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 94 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 172 2 18 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 172 (accept_3_3 35 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 172 2 17 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 94 172 2 16 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 94 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 172 2 15 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 172 (accept_3_3 29 94 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 172 2 14 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 172 2 13 47 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 172 2 12 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 94 172 (accept_3_3 23 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94
  172 2 11 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  94 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 94 172 2 10 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 94 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 94 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 172 2 9 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 172 (accept_3_3 17 94 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 172 2 8 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 94 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 172 2 7 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 94 172 2 6 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 94 172 (accept_3_3 11 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94
  172 2 5 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  94 172 (Polychromatic418967fa.accept_23_9_2_11_1_9732 9 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 94 172 2 4 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 94 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 172 2 3 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 172 (accept_3_3 5 94 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 172 2 2 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 94 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 172 2 1 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 93 172
  (Eq.refl Bool.true) (allA_succ_of_accept 79 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 93 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 93 172 (accept_3_3 77 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  93 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 93 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 172 (accept_3_3 74 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 172
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 93 172 (accept_3_3 71 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  93 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 93 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 172 (accept_3_3 68 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 93 172 (accept_3_3 65 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  93 172 (Polychromatic418967fa.accept_11_9_5_7_1_815 64 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 93 172 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 172 (accept_3_3 62 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 93 172 (accept_3_3 59 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  93 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 93 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 172 (accept_3_3 56 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 172 (accept_3_3 53 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 172 (accept_3_3 50 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 172 (accept_3_3 47 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 172 (Polychromatic418967fa.accept_22_2_5_18_1_9731 46 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 172 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 172 (accept_3_3 44 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 172 (accept_3_3 41 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 172 (Polychromatic418967fa.accept_20_19_13_12_1_2476 39 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 172 (accept_3_3 38 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 172
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 172 (accept_3_3 35 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 172 (accept_3_3 32 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 172 (accept_3_3 29 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 172 (Polychromatic418967fa.accept_17_11_8_2_1_3398 28 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 172 (accept_3_3 26 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 172 (accept_3_3 23 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 172 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 172 (accept_3_3 20 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 172 (accept_3_3 17 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 172 (accept_3_3 14 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 172 (accept_3_3 11 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 172 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 172 (accept_3_3 8 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 172 (accept_3_3 5 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 93 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 172 (Polychromatic418967fa.accept_19_3_17_1_1_781 3 93 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 172 (accept_3_3 2 93 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 92 172 (Eq.refl
  Bool.true) (allA_of_3_1 81 92 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 91 172 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 172 (accept_3_3 80 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 91 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 172 (Polychromatic418967fa.accept_19_2_15_1_1_3977
  78 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 172 (accept_3_3 77
  91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 172
  (Polychromatic418967fa.accept_10_6_1_2_1_874 76 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 172 (accept_3_3 74 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 172 (Polychromatic418967fa.accept_10_3_1_2_1_521 73 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 172 (Polychromatic418967fa.accept_16_8_11_12_1_962
  72 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 172 (accept_3_3 71
  91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 172
  (Polychromatic418967fa.accept_11_4_3_7_1_828 70 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 172 (accept_3_3 68 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 91 172 (Polychromatic418967fa.accept_14_11_7_4_1_3449 67 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 172
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 172 (accept_3_3 65 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 172 (Polychromatic418967fa.accept_17_13_6_2_1_5850 64 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 172 (accept_3_3 62 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 172 (Polychromatic418967fa.accept_19_4_15_1_1_2819 61 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 172
  (Polychromatic418967fa.accept_21_18_7_4_1_8131 60 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 172 (accept_3_3 59 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 172 (accept_3_3 56 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 172
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 172 (accept_3_3 53 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 172 (accept_3_3 50 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 172 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 172
  (Polychromatic418967fa.accept_11_4_3_7_1_828 48 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 172 (accept_3_3 47 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 172 (accept_3_3 44 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 172 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 172
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 42 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 91 172 (accept_3_3 41 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 91 172 (Polychromatic418967fa.accept_15_10_1_7_1_5207 40 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 172 (accept_3_3 38 91 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 172 (Polychromatic418967fa.accept_11_4_3_7_1_828
  37 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 172
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 172 (accept_3_3 35 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 172 (accept_3_3 32 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 172
  (Polychromatic418967fa.accept_17_13_6_2_1_5850 30 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 172 (accept_3_3 29 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 172 (Polychromatic418967fa.accept_22_6_3_18_1_8074 28 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 172 (accept_3_3 26 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 172 (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 172
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 172 (accept_3_3 23 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 172 (accept_3_3 20 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 172 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 172
  (Polychromatic418967fa.accept_17_1_6_2_1_623 18 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 172 (accept_3_3 17 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 172 (accept_3_3 14 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 172 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 172
  (Polychromatic418967fa.accept_17_12_6_2_1_2346 12 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 172 (accept_3_3 11 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 172 (accept_3_3 8 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 172
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 172 (accept_3_3 5 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  172 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 91 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 172 (accept_3_3 2 91 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 172 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 91 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 90 172 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 90 172 2 41 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 90 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 90 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 172 2 40 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 172 2 39 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 172 (accept_3_3 77 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90
  172 2 38 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  90 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 90 172 2 37 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 90 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 90 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 172 2 36 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 172 (accept_3_3 71 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 172 2 35 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 172 2 34 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 90 172 (Polychromatic418967fa.accept_13_2_12_3_1_415 67 90 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 172 2 33 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 172 (accept_3_3 65 90 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 172 2 32 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 172 2 31 45 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 172 2 30 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 172 (accept_3_3 59 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90
  172 2 29 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  90 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 90 172 2 28 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 90 172 (Polychromatic418967fa.accept_19_17_14_1_1_6825 55 90 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 172 2 27 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 172 (accept_3_3 53 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 172 2 26 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 172 2 25 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 172 (Polychromatic418967fa.accept_21_7_6_4_1_3445 49 90 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 172 2 24 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 172 (accept_3_3 47 90 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 172 2 23 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 172 2 22 45 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 172
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 172 2 21 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 172 (accept_3_3 41 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90
  172 2 20 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  90 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 90 172 2 19 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 90 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 172 2 18 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 172 (accept_3_3 35 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 172 2 17 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 172 2 16 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 172 2 15 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 172 (accept_3_3 29 90 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 172 2 14 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 172 2 13 45 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 172
  (Polychromatic418967fa.accept_19_6_14_1_1_2752 25 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 172 2 12 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 172 (accept_3_3 23 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90
  172 2 11 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  90 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 90 172 2 10 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 90 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 172 2 9 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 172 (accept_3_3 17 90 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 172 2 8 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 172 2 7 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 172
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 172 2 6 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 172 (accept_3_3 11 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 172 2 5 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 172 2 4 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 172 (Polychromatic418967fa.accept_21_7_6_4_1_3445 7 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 172 2 3 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 172 (accept_3_3 5 90 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 172 2 2 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 172 2 1 45 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 172
  (Polychromatic418967fa.accept_22_1_2_18_1_9730 1 90 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 89
  172 (Eq.refl Bool.true) (allA_of_3_1 84 89 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 88 172 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 88 172 4 21 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 88 172 (accept_3_3 83 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 88 172 2 41 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 88 172 (Polychromatic418967fa.accept_15_6_13_7_1_222 81 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 172 4 20 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 172 (Polychromatic418967fa.accept_16_15_8_12_1_2737
  79 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 172 2 39 44 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 88 172 (accept_3_3 77
  88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88 172 4 19 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 75 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 88 172 2 37 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 88 172 (Polychromatic418967fa.accept_16_9_8_12_1_979 73 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 172 4 18 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 172 (accept_3_3 71 88 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 172 2 35 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 88 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 172 4 17 22 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 172 2 33 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 88 172 (accept_3_3 65 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88
  172 4 16 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  88 172 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 172 2 31 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 172 (Polychromatic418967fa.accept_16_13_8_12_1_2723 61 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 172 4 15 22 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 172 (accept_3_3 59 88 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 172 2 29 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 172 4 14 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 88 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 55 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 172 2 27 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 172 (accept_3_3 53 88 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 172 4 13 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 88 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 172 2 25 44 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 172 4 12 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 172 (accept_3_3 47 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88
  172 2 23 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  88 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 88 172 4 11 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 88 172 (Polychromatic418967fa.accept_16_11_8_12_1_1767 43 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 172 2 21 44 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 172 (accept_3_3 41 88 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 172 4 10 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 88 172 2 19 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 88 172 (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 172 4 9 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 172 (accept_3_3 35 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 88 172 2 17 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 88 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 172 4 8 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 172 2 15 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 172 (accept_3_3 29 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  172 4 7 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 172 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 172 2 13 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 172 4 6 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 172 (accept_3_3 23 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 172 2 11 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 172 4 5 22 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 172
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 172 2 9 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 172 (accept_3_3 17 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  172 4 4 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 172 2 7 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 172 4 3 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 172 (accept_3_3 11 88 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 172 2 5 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 172 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 88 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 172 4 2 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 172
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 172 2 3 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 172 (accept_3_3 5 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 172
  4 1 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  172 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 88 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 172 2 1 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 172 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 88 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 87 172
  (Eq.refl Bool.true) (allA_succ_of_accept 85 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 87 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 87 172 (accept_3_3 83 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  87 172 (Polychromatic418967fa.accept_16_2_7_12_1_3793 82 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 87 172 (Polychromatic418967fa.accept_15_6_12_7_1_1360 81 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 172 (accept_3_3 80 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 87 172 (accept_3_3 77 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  87 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 87 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 172 (accept_3_3 74 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 172
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 87 172 (accept_3_3 71 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  87 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 87 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 172 (accept_3_3 68 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 87 172 (accept_3_3 65 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  87 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 87 172 (Polychromatic418967fa.accept_14_7_3_4_1_1816 63 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 172 (accept_3_3 62 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 172
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 87 172 (accept_3_3 59 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  87 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 87 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 172 (accept_3_3 56 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 172 (accept_3_3 53 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 172 (accept_3_3 50 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 172 (accept_3_3 47 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 172 (Polychromatic418967fa.accept_13_7_9_3_1_1504 46 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 172 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 172 (accept_3_3 44 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 172 (accept_3_3 41 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 172 (accept_3_3 38 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 172 (accept_3_3 35 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 172 (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 172 (accept_3_3 32 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 172 (accept_3_3 29 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 172 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 172 (accept_3_3 26 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 172 (accept_3_3 23 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 172 (accept_3_3 20 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 172 (accept_3_3 17 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 172 (accept_3_3 14 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 172 (accept_3_3 11 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 172 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 172 (accept_3_3 8 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 172 (accept_3_3 5 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 87 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 172 (accept_3_3 2 87 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 172
  (allA_of_3_1 86 86 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 172 (allA_succ_of_accept 84 85 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 172 (accept_3_3 83 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 172 (accept_3_3 80 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 172 (accept_3_3 77 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 172 (Polychromatic418967fa.accept_13_11_7_3_1_894 76 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 172 (accept_3_3 74 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 172
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 72 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 172 (accept_3_3 71 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 172 (accept_3_3 68 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 67 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 172 (accept_3_3 65 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 172 (Polychromatic418967fa.accept_15_4_10_7_1_1356 64 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 172 (accept_3_3 62 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 172 (accept_3_3 59 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 172 (accept_3_3 56 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 172 (Polychromatic418967fa.accept_16_7_5_12_1_4824 55 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 172 (accept_3_3 53 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 172 (accept_3_3 50 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 172 (accept_3_3 47 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 172 (accept_3_3 44 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 172 (accept_3_3 41 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 172 (accept_3_3 38 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 172
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 172 (accept_3_3 35 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 172 (accept_3_3 32 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 172 (accept_3_3 29 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 172 (accept_3_3 26 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 172 (accept_3_3 23 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 172 (accept_3_3 20 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 172 (accept_3_3 17 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 172 (accept_3_3 14 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 172 (accept_3_3 11 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 172 (accept_3_3 8 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 172 (accept_3_3 5 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  172 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 85 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 172 (accept_3_3 2 85 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 172
  (allA_succ_of_accept 83 84 172 (accept_3_3 83 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  172 2 41 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  84 172 (Polychromatic418967fa.accept_16_1_4_12_1_376 81 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 172 4 20 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 172 2 39 42 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 172 (accept_3_3 77 84 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 172 4 19 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 172
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 75 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 172 2 37 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 73 84 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 172 4 18 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 172 (accept_3_3 71 84 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 172 2 35 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 172 4 17 21 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 172 2 33 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 172 (accept_3_3 65 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84
  172 4 16 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  84 172 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 84 172 2 31 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 84 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 172 4 15 21 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 172 (accept_3_3 59 84 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 172 2 29 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 172
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 172 4 14 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 172 (Polychromatic418967fa.accept_16_7_4_12_1_1806 55 84 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 172 2 27 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 172 (accept_3_3 53 84 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 172 4 13 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 172 2 25 42 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 172 4 12 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 172 (accept_3_3 47 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84
  172 2 23 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  84 172 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 172 4 11 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 172 2 21 42 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 172 (accept_3_3 41 84 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 172 4 10 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 172
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 172 2 19 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 84 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 172 4 9 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 172 (accept_3_3 35 84 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 172 2 17 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 172 4 8 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 172 2 15 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 172 (accept_3_3 29 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  172 4 7 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 84 172 2 13 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 84 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 172 4 6 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 172 (accept_3_3 23 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 172 2 11 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 172 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  21 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 172 4 5 21 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 172
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 172 2 9 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 172 (accept_3_3 17 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  172 4 4 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 172 2 7 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 172 4 3 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 172 (accept_3_3 11 84 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 172 2 5 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 84 172 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 172 4 2 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 172 2 3 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 172 (accept_3_3 5 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 172
  4 1 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84
  172 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 84 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 84 172 2 1 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 84 172 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 84 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 172 (allA_of_3_1
  83 83 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 172 (allA_succ_of_accept 81 82 172
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 172 2 40 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 82 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 82 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 172 2 39 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 172 (accept_3_3 77 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 172 2 38 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 172 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 172 2 37 41 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 172 2 36 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 172 (accept_3_3 71 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  172 2 35 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 172 2 34 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 82 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 172 2 33 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 172 (accept_3_3 65 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 172 2 32 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 172
  (Polychromatic418967fa.accept_16_15_2_12_1_1799 63 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 172 2 31 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 82 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 172 2 30 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 172 (accept_3_3 59 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 172 2 29 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 172 2 28 41 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 172 2 27 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 172 (accept_3_3 53 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  172 2 26 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 172 2 25 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 172 2 24 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 172 (accept_3_3 47 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 172 2 23 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 172
  (Polychromatic418967fa.accept_19_7_6_1_1_796 45 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 172 2 22 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 172 2 21 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 172 (accept_3_3 41 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 172 2 20 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 172 (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 172 2 19 41 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 172 2 18 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 172 (accept_3_3 35 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  172 2 17 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 172 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 172 2 16 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 172 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 82 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 172 2 15 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 172 (accept_3_3 29 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 172 2 14 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 172 2 13 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 82 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 172 2 12 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 172 (accept_3_3 23 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 172 2 11 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 172 (Polychromatic418967fa.accept_19_2_6_1_1_9729 21 82 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 172 2 10 41 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 172 2 9 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 172 (accept_3_3 17 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  172 2 8 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 172 2 7 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 172 2 6 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 172 (accept_3_3 11 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 172 2 5 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 82 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 172 2 4 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 172 2 3 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 172 (accept_3_3 5 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 172
  2 2 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  172 (Polychromatic418967fa.accept_17_3_14_2_1_646 3 82 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 82 172 2 1 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 82 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 172
  (allA_succ_of_accept 80 81 172 (accept_3_3 80 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 78 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 172 (accept_3_3 77 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 172
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 75 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 172 (accept_3_3 74 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 172 (Polychromatic418967fa.accept_15_12_6_7_1_1353 72 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 172 (accept_3_3 71 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 172 (Polychromatic418967fa.accept_21_7_18_4_1_5024 70 81
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 172
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 172 (accept_3_3 68 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 172 (accept_3_3 65 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 172 (Polychromatic418967fa.accept_14_8_11_4_1_3438 64 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 172
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 172 (accept_3_3 62 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 172 (Polychromatic418967fa.accept_19_3_5_1_1_6811 60 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 172 (accept_3_3 59 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 172 (Polychromatic418967fa.accept_11_3_4_7_1_114 58 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 172
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 172 (accept_3_3 56 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 172 (accept_3_3 53 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 172 (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 172
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 51 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 172 (accept_3_3 50 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 172 (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 172 (accept_3_3 47 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 172
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 172 (accept_3_3 44 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 172 (accept_3_3 41 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 172 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 172
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 172 (accept_3_3 38 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 172 (accept_3_3 35 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 172 (Polychromatic418967fa.accept_16_2_1_12_1_3798 34 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 172
  (Polychromatic418967fa.accept_10_3_1_2_1_521 33 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 172 (accept_3_3 32 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 172 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 172 (accept_3_3 29 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 172 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 172
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 172 (accept_3_3 26 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 172 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 172 (accept_3_3 23 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 172 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 172
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 172 (accept_3_3 20 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 172 (accept_3_3 17 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 172
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 172 (accept_3_3 14 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 172 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 172 (accept_3_3 11 81 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 172 (Polychromatic418967fa.accept_44_10_37_40_1_9728 10 81
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 172
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 172 (accept_3_3 8 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 81 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 172 (accept_3_3 5 81 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 172 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 81 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 172 (Polychromatic418967fa.accept_10_3_1_2_1_521 3
  81 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 172 (accept_3_3 2 81 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 172 (allA_of_3_1 80
  80 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 172 (allA_succ_of_accept 78 79 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 172 (accept_3_3 77 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 172 (accept_3_3 74 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 172 (Polychromatic418967fa.accept_19_16_3_1_1_5389 73 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 172
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 172 (accept_3_3 71 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 172 (accept_3_3 68 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 172 (accept_3_3 65 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298 64 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 172 (accept_3_3 62 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 172 (accept_3_3 59 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 172 (accept_3_3 56 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 172 (accept_3_3 53 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 172 (Polychromatic418967fa.accept_16_4_15_12_1_1745 52 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 172 (accept_3_3 50 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 172 (accept_3_3 47 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 172 (accept_3_3 44 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 172 (accept_3_3 41 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 172 (accept_3_3 38 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 172
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 172 (accept_3_3 35 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 172 (accept_3_3 32 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 172 (accept_3_3 29 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 172 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 172 (accept_3_3 26 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 172 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 172 (accept_3_3 23 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 172 (accept_3_3 20 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 172
  (Polychromatic418967fa.accept_13_5_1_3_1_878 18 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 172 (accept_3_3 17 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 172 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 172 (accept_3_3 14 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 172 (accept_3_3 11 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 172 (accept_3_3 8 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 172 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 172 (accept_3_3 5 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 172 (accept_3_3 2 79 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 79 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 172
  (allA_succ_of_accept 77 78 172 (accept_3_3 77 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  172 2 38 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  78 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 172 2 37 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 172 2 36 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 172 (accept_3_3 71 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 172 2 35 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 172 2 34 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 78 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 172 2 33 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 172 (accept_3_3 65 78 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 172 2 32 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 172 2 31 39 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 172 2 30 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 172 (accept_3_3 59 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78
  172 2 29 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  78 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 78 172 2 28 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 78 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 55 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 172 2 27 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 172 (accept_3_3 53 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 172 2 26 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 172
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 172 2 25 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 172 2 24 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 172 (accept_3_3 47 78 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 172 2 23 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 172 2 22 39 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 172 2 21 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 172 (accept_3_3 41 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78
  172 2 20 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  78 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 78 172 2 19 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 172 (Polychromatic418967fa.accept_19_18_2_1_1_5375 37 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 172 2 18 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 172 (accept_3_3 35 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 172 2 17 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 172 2 16 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 172 2 15 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 172 (accept_3_3 29 78 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 172 2 14 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 172 2 13 39 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 172 2 12 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 172 (accept_3_3 23 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  172 2 11 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 172 2 10 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 172 2 9 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 172 (accept_3_3 17 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 172 2 8 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 172 2 7 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 172 2 6 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 172 (accept_3_3 11 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  172 2 5 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 172 2 4 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 172 2 3 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 172 (accept_3_3 5 78 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 172 2 2 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 172 2 1 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 172
  (Polychromatic418967fa.accept_25_1_3_22_1_9727 1 78 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 172
  (allA_of_3_1 77 77 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 172 (allA_succ_of_accept 75 76 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 172 2 37 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 76 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 172 4 18 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 172 (accept_3_3 71 76 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 172 2 35 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 76 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 172 4 17 19 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 172
  (Polychromatic418967fa.accept_13_2_11_3_1_873 67 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 172 2 33 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 172 (accept_3_3 65 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  172 4 16 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 172 (Polychromatic418967fa.accept_23_17_7_11_1_6113 63 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 172 2 31 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 172 4 15 19 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 172 (accept_3_3 59 76 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 172 2 29 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 172 4 14 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 172 (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 76 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 172 2 27 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 172 (accept_3_3 53 76 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 172 4 13 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 172 2 25 38 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 172
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 172 4 12 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 172 (accept_3_3 47 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  172 2 23 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 172 4 11 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 172 2 21 38 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 172 (accept_3_3 41 76 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 172 4 10 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 172 2 19 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 172 4 9 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 172 (accept_3_3 35 76 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 172 2 17 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 172 4 8 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 172 2 15 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 172 (accept_3_3 29 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  172 4 7 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 172 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 172 2 13 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 172 4 6 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 172 (accept_3_3 23 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 172 2 11 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 172 4 5 19 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 172 2 9 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 172 (accept_3_3 17 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  172 4 4 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 172 2 7 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 172 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 172 4 3 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 172 (accept_3_3 11 76 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 172 2 5 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 172 4 2 19 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 172 2 3 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 172 (accept_3_3 5 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 172
  4 1 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 172 2 1 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 76 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 172 (allA_succ_of_accept
  74 75 172 (accept_3_3 74 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 172 (accept_3_3 71 75 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 69
  75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 172 (accept_3_3 68 75
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 172 (accept_3_3 65 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 172 (accept_3_3 62 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 172 (accept_3_3 59 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 172 (accept_3_3 56 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 172 (accept_3_3 53 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 172 (accept_3_3 50 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 172 (accept_3_3 47 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 172 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 172 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 172 (accept_3_3 44 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 172 (accept_3_3 41 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 172 (accept_3_3 38 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 172 (accept_3_3 35 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 172 (accept_3_3 32 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 172 (accept_3_3 29 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 172 (accept_3_3 26 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 172 (accept_3_3 23 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 172 (Polychromatic418967fa.accept_19_2_18_1_1_8275 21 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 172 (accept_3_3 20 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 172 (accept_3_3 17 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 172 (accept_3_3 14 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 172
  (Polychromatic418967fa.accept_17_12_7_2_1_4561 12 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 172 (accept_3_3 11 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 172 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 172 (accept_3_3 8 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 172 (accept_3_3 5 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 75 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 172 (accept_3_3 2 75 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 172 (allA_of_3_1 74 74
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 172 (allA_succ_of_accept 72 73 172
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 172 (accept_3_3 71 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 172 (accept_3_3 68 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 172 (Polychromatic418967fa.accept_16_3_9_12_1_4831 67 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 172
  (Polychromatic418967fa.accept_15_6_13_7_1_222 66 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 172 (accept_3_3 65 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 172 (accept_3_3 62 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 172
  (Polychromatic418967fa.accept_19_3_16_1_1_8246 60 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 172 (accept_3_3 59 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 172 (accept_3_3 56 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 172
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 54 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 172 (accept_3_3 53 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 172 (Polychromatic418967fa.accept_16_4_9_12_1_4829 52 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 172 (accept_3_3 50 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 172 (Polychromatic418967fa.accept_14_7_3_4_1_1816 49 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 172 (accept_3_3 47 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 172 (accept_3_3 44 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 172
  (Polychromatic418967fa.accept_19_4_16_1_1_8332 42 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 172 (accept_3_3 41 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 172 (Polychromatic418967fa.accept_16_8_9_12_1_1737 40 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 172 (accept_3_3 38 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 172 (accept_3_3 35 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 172 (accept_3_3 32 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 172 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 172
  (Polychromatic418967fa.accept_20_10_13_12_1_9726 30 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 73 172 (accept_3_3 29 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 73 172 (Polychromatic418967fa.accept_22_6_7_18_1_9725 28 73 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 172 (accept_3_3 26 73 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 172 (Polychromatic418967fa.accept_10_5_3_2_1_899
  25 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 172
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 172 (accept_3_3 23 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 172 (accept_3_3 20 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 172 (Polychromatic418967fa.accept_16_3_9_12_1_4831 19 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 172
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 172 (accept_3_3 17 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 172 (Polychromatic418967fa.accept_17_16_5_2_1_9724 16 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 172 (accept_3_3 14 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 172
  (Polychromatic418967fa.accept_22_12_7_18_1_9723 12 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 172 (accept_3_3 11 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 172 (accept_3_3 8 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 172 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 172 (accept_3_3 5 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  172 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 73 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 172 (accept_3_3 2 73 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 172 (allA_succ_of_accept 71
  72 172 (accept_3_3 71 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 172 2 35 36 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 172 4 17 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 67 72 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 172 2 33 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 172 (accept_3_3 65 72 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 172 4 16 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 172 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 72 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 172 2 31 36 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 172 4 15 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 172 (accept_3_3 59 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  172 2 29 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 172 (Polychromatic418967fa.accept_16_9_8_12_1_979 57 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 172 4 14 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 172 2 27 36 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 172 (accept_3_3 53 72 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 172 4 13 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 172
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 172 2 25 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 172 (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 72 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 172 4 12 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 172 (accept_3_3 47 72 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 172 2 23 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 72 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 172 4 11 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 172
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 172 2 21 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 172 (accept_3_3 41 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  172 4 10 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 172 (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 172 2 19 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 172 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 172 4 9 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 172 (accept_3_3 35 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 172 2 17 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 172 4 8 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 172
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 172 2 15 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 172 (accept_3_3 29 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72
  172 4 7 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  72 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 72 172 2 13 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 72 172 (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 172 4 6 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 172 (accept_3_3 23 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 172 2 11 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 172 (Polychromatic418967fa.accept_13_8_7_3_1_430 21
  72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 172 4 5 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 172 2 9 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 172 (accept_3_3 17 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  172 4 4 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 172 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 172 2 7 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 72 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 172 4 3 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 172 (accept_3_3 11 72 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 172 2 5 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 72 172 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 172 4 2 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 172
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 172 2 3 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 172 (accept_3_3 5 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 172
  4 1 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72
  172 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 72 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 72 172 2 1 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 72 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 72 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 172 (allA_of_3_1 71 71 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 172 (allA_succ_of_accept 69 70 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 172 2 34 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 172 2 33 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 172 (accept_3_3 65 70 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 172 2 32 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 172 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 172 2 31 35 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 172 2 30 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 172 (accept_3_3 59 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  172 2 29 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 172 2 28 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 70 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 70 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 172 2 27 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 172 (accept_3_3 53 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 172 2 26 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 172 2 25 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 70 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 172 2 24 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 172 (accept_3_3 47 70 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 172 2 23 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 172 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 172 2 22 35 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 172 2 21 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 172 (accept_3_3 41 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  172 2 20 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 172 2 19 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 172 2 18 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 172 (accept_3_3 35 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 172 2 17 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 172 2 16 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 172 2 15 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 172 (accept_3_3 29 70 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 172 2 14 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 172 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 172 2 13 35 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 172
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 172 2 12 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 172 (accept_3_3 23 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  172 2 11 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 172 2 10 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 172 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 70 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 172 2 9 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 172 (accept_3_3 17 70 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 172 2 8 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 70 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 172 2 7 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 172 2 6 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 172 (accept_3_3 11 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  172 2 5 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 172 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 172 2 4 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 172 2 3 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 172 (accept_3_3 5 70 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 172 2 2 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 172 2 1 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 172
  (allA_succ_of_accept 68 69 172 (accept_3_3 68 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 172 (accept_3_3 65 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 172 (Polychromatic418967fa.accept_13_12_4_3_1_1528 64 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 172
  (Polychromatic418967fa.accept_18_9_15_10_1_395 63 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 172 (accept_3_3 62 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 172 (Polychromatic418967fa.accept_18_6_15_10_1_6975 60 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 172 (accept_3_3 59 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 69 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 172
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 172 (accept_3_3 56 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 172 (accept_3_3 53 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 172 (accept_3_3 50 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 172 (accept_3_3 47 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 172 (Polychromatic418967fa.accept_13_7_4_3_1_3064 46 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 172 (accept_3_3 44 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 172 (accept_3_3 41 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 172 (accept_3_3 38 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 172 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 172 (accept_3_3 35 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 69 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 172 (accept_3_3 32 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 172 (accept_3_3 29 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 172
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 172 (accept_3_3 26 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 172 (accept_3_3 23 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 172 (accept_3_3 20 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 172 (accept_3_3 17 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 172
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 172 (accept_3_3 14 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 172 (accept_3_3 11 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 172 (accept_3_3 8 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 172 (accept_3_3 5 69 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 69 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 172 (accept_3_3 2 69 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 172 (allA_of_3_1 68 68 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 172 (allA_succ_of_accept 66 67 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 172 (accept_3_3 65 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 172 (accept_3_3 62 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 172 (accept_3_3 59 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 172 (accept_3_3 56 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 172 (accept_3_3 53 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 172 (accept_3_3 50 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 172 (accept_3_3 47 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 172 (accept_3_3 44 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 172 (accept_3_3 41 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 172 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 172 (accept_3_3 38 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 172 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 172
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 172 (accept_3_3 35 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 172 (accept_3_3 32 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 172 (accept_3_3 29 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 172 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 172 (accept_3_3 26 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 172 (accept_3_3 23 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 172 (accept_3_3 20 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 172
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 172 (accept_3_3 17 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 172 (accept_3_3 14 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 172 (Polychromatic418967fa.accept_19_13_10_1_1_8236 13 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 172 (accept_3_3 11 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 172 (accept_3_3 8 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 172 (accept_3_3 5 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 172 (accept_3_3 2 67 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 172 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 67 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 172 (allA_succ_of_accept 65 66
  172 (accept_3_3 65 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 172 2 32 33 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 172
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 172 2 31 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 172 2 30 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 172 (accept_3_3 59 66 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 172 2 29 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 172 2 28 33 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 172 2 27 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 172 (accept_3_3 53 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  172 2 26 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 172 2 25 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 172 2 24 33 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 172 (accept_3_3 47 66 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 172 2 23 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 172 2 22 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 172 2 21 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 172 (accept_3_3 41 66 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 172 2 20 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 172 2 19 33 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 172
  (Polychromatic418967fa.accept_13_11_1_3_1_910 37 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 172 2 18 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 172 (accept_3_3 35 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  172 2 17 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 172 2 16 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 172 2 15 33 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 172 (accept_3_3 29 66 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 172 2 14 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 172 2 13 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 172 2 12 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 172 (accept_3_3 23 66 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 172 2 11 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 172 2 10 33 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 172
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 172 2 9 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 172 (accept_3_3 17 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  172 2 8 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 172 2 7 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 172 2 6 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 172 (accept_3_3 11 66 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 172 2 5 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 172 2 4 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 172 2 3 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 172 (accept_3_3 5 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 172
  2 2 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  172 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 172 2 1 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 172 (allA_of_3_1 65 65 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 172
  (allA_succ_of_accept 63 64 172 (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 64 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 172 2 31 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 61
  64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 172 4 15 16 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 172 (accept_3_3 59
  64 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 172 2 29 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 172
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 172 4 14 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 172 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 64 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 172 2 27 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 172 (accept_3_3 53 64 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 172 4 13 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 172 (Polychromatic418967fa.accept_19_13_7_1_1_5379 51 64 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 172 2 25 32 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 172
  (Polychromatic418967fa.accept_11_5_9_7_1_411 49 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 172 4 12 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 172 (accept_3_3 47 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  172 2 23 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 172 4 11 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 172 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 64 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 172 2 21 32 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 172 (accept_3_3 41 64 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 172 4 10 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 172
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 172 2 19 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 172 4 9 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 172 (accept_3_3 35 64 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 64 172 2 17 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 64 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 172 4 8 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 172 2 15 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 172 (accept_3_3 29 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  172 4 7 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 172 2 13 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 172 (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 64 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 172 4 6 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 172 (accept_3_3 23 64 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 172 2 11 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 172 (Polychromatic418967fa.accept_19_2_7_1_1_2808
  21 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 172 4 5 16 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 172 2 9 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 172 (accept_3_3 17 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  172 4 4 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 172 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 172 2 7 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 172 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 64 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 172 4 3 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 172 (accept_3_3 11 64 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 172 2 5 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 172 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 64 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 172 4 2 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 172
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 172 2 3 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 172 (accept_3_3 5 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 172
  4 1 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 172 2 1 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 172 (Polychromatic418967fa.accept_17_1_13_2_1_7086 1 64 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 172 (allA_succ_of_accept 62 63 172 (accept_3_3 62 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 63 172 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 172 (accept_3_3 59 63 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 172 (Polychromatic418967fa.accept_17_7_12_2_1_7105
  58 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 172
  (Polychromatic418967fa.accept_13_5_11_3_1_902 57 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 172 (accept_3_3 56 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 172 (accept_3_3 53 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 172
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 172 (accept_3_3 50 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 172 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 172 (accept_3_3 47 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 172 (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 172
  (Polychromatic418967fa.accept_10_5_3_2_1_899 45 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 172 (accept_3_3 44 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 172 (accept_3_3 41 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 172 (Polychromatic418967fa.accept_13_1_11_3_1_901 40 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 172
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 172 (accept_3_3 38 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 172 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 172 (accept_3_3 35 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 172 (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 63
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 172
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 172 (accept_3_3 32 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 172 (accept_3_3 29 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 172
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 172 (accept_3_3 26 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 172 (accept_3_3 23 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 172 (Polychromatic418967fa.accept_19_3_6_1_1_4064 22 63 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 172
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 172 (accept_3_3 20 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 172 (accept_3_3 17 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 172 (Polychromatic418967fa.accept_24_16_15_4_1_9722 16 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 172
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 172 (accept_3_3 14 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 172 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 172 (accept_3_3 11 63 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 172 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 63
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 172
  (Polychromatic418967fa.accept_20_9_3_12_1_6627 9 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 172 (accept_3_3 8 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 172 (accept_3_3 5 63 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 172 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 63 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 172 (accept_3_3 2 63 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 172 (allA_of_3_1 62 62 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 172 (allA_succ_of_accept 60 61 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 172 (accept_3_3 59 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 172 (accept_3_3 56 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 172
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 172 (accept_3_3 53 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 172 (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 172 (accept_3_3 50 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 172 (accept_3_3 47 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 172 (accept_3_3 44 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 172 (accept_3_3 41 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 172 (accept_3_3 38 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 172 (accept_3_3 35 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 172 (accept_3_3 32 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 172 (accept_3_3 29 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 172 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 172 (accept_3_3 26 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 172 (accept_3_3 23 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 172 (accept_3_3 20 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 172 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 172
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 172 (accept_3_3 17 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 172 (accept_3_3 14 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 172 (accept_3_3 11 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 172 (accept_3_3 8 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 172 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 61 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 172 (accept_3_3 5 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 172 (accept_3_3 2 61 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 172 (allA_succ_of_accept 59 60 172 (accept_3_3 59 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 172 2 29 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 172 4 14 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 172 (Polychromatic418967fa.accept_17_4_9_2_1_9721
  55 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 172 2 27 30 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 172 (accept_3_3 53
  60 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 172 4 13 15 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 172
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 51 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 172 2 25 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 172 4 12 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 172 (accept_3_3 47 60 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 172 2 23 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 172 (Polychromatic418967fa.accept_17_11_9_2_1_8423 45 60 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 172 4 11 15 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 172 2 21 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 172 (accept_3_3 41 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  172 4 10 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 172 2 19 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 172 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 60 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 172 4 9 15 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 172 (accept_3_3 35 60 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 172 2 17 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 172 (Polychromatic418967fa.accept_13_7_8_3_1_1533
  33 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 172 4 8 15 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 172 2 15 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 172 (accept_3_3 29 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  172 4 7 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 172 (Polychromatic418967fa.accept_21_6_18_4_1_4952 27 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 172 2 13 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 172 4 6 15 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 172 (accept_3_3 23 60 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 172 2 11 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 172 4 5 15 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 172
  (Polychromatic418967fa.accept_21_19_18_4_1_4977 19 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 172 2 9 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 172 (accept_3_3 17 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  172 4 4 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 172 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 172 2 7 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 172 4 3 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 172 (accept_3_3 11 60 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 172 2 5 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 172 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 172 4 2 15 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 172
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 172 2 3 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 172 (accept_3_3 5 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 172
  4 1 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 172 2 1 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 172 (Polychromatic418967fa.accept_21_1_18_4_1_4975 1 60 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 172 (allA_of_3_1 59 59 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 172
  (allA_succ_of_accept 57 58 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 58 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 172 2 28 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 55
  58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 172 2 27 29 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 172 (accept_3_3 53
  58 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 172 2 26 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 172 2 25 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 172 2 24 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 172 (accept_3_3 47 58 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 172 2 23 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 58 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 172 2 22 29 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 172 2 21 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 172 (accept_3_3 41 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  172 2 20 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 172 2 19 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 172 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 58 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 172 2 18 29 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 172 (accept_3_3 35 58 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 172 2 17 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 172 2 16 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 172 2 15 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 172 (accept_3_3 29 58 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 172 2 14 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 172 2 13 29 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 172 2 12 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 172 (accept_3_3 23 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  172 2 11 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 172 2 10 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 172 2 9 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 172 (accept_3_3 17 58 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 172 2 8 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 58 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 172 2 7 29 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 172 2 6 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 172 (accept_3_3 11 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  172 2 5 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 172 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 172 2 4 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 172 2 3 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 172 (accept_3_3 5 58 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 172 2 2 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 58 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 172 2 1 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 58 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 172 (allA_succ_of_accept 56
  57 172 (accept_3_3 56 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 172 (accept_3_3 53 57 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 172 (accept_3_3 50 57
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 172
  (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 172 (accept_3_3 47 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 172 (Polychromatic418967fa.accept_17_12_6_2_1_2346 46 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 172 (accept_3_3 44 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 172 (accept_3_3 41 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 172 (accept_3_3 38 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 172
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 172 (accept_3_3 35 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 172 (accept_3_3 32 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 172 (accept_3_3 29 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 172 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 172 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 172 (accept_3_3 26 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 172
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 172 (accept_3_3 23 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 172 (accept_3_3 20 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 172
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 172 (accept_3_3 17 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 172 (accept_3_3 14 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 172 (accept_3_3 11 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 172 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 172 (accept_3_3 8 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 172 (accept_3_3 5 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 57 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 172 (accept_3_3 2 57 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 172)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 172 (allA_of_3_1 56 56 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 172
  (allA_succ_of_accept 54 55 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 172 (accept_3_3 53 55 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 172 (accept_3_3 50 55
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 172
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 55 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 172 (accept_3_3 47 55 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 172 (accept_3_3 44 55
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 172 (Polychromatic418967fa.accept_8_3_7_4_1_42
  43 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 172
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 42 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 172 (accept_3_3 41 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 172 (accept_3_3 38 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 172
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 172 (accept_3_3 35 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 172 (accept_3_3 32 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 172 (accept_3_3 29 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 172 (accept_3_3 26 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 172 (Polychromatic418967fa.accept_20_5_15_12_1_9720 25 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 172 (accept_3_3 23 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 172 (accept_3_3 20 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 172
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 172 (accept_3_3 17 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 172 (accept_3_3 14 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 172 (accept_3_3 11 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 172 (accept_3_3 8 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 172 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 172
  (Polychromatic418967fa.accept_17_6_4_2_1_5889 6 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 172 (accept_3_3 5 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  172 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 55 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 172 (accept_3_3 2 55 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 172 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 55 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 172 (allA_succ_of_accept 53 54 172
  (accept_3_3 53 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 172 2 26 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 172 2 25 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 172 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 54 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 172 2 24 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 172 (accept_3_3 47 54 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 172 2 23 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 54 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 172 2 22 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 172 2 21 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 172 (accept_3_3 41 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  172 2 20 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 172 2 19 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 172 2 18 27 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 172 (accept_3_3 35 54 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 172 2 17 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 172 2 16 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 172 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 54 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 172 2 15 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 172 (accept_3_3 29 54 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 172 2 14 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 172 2 13 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 172
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 172 2 12 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 172 (accept_3_3 23 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  172 2 11 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 172 2 10 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 172 (Polychromatic418967fa.accept_21_19_12_4_1_8134 19 54 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 172 2 9 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 172 (accept_3_3 17 54 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 172 2 8 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 172 2 7 27 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 172 2 6 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 172 (accept_3_3 11 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  172 2 5 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 172 2 4 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 172 2 3 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 172 (accept_3_3 5 54 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 172 2 2 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 172 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 54 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 172 2 1 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 172)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 172 (allA_of_3_1 53 53 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 172 (allA_succ_of_accept 51 52 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 172 2 25 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 172 4 12 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 172 (accept_3_3 47 52 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 172 2 23 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 172 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 52
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 172 4 11 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 172 2 21 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 172 (accept_3_3 41 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  172 4 10 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 172 2 19 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 172 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 52 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 172 4 9 13 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 172 (accept_3_3 35 52 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 172 2 17 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 172 4 8 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 172 2 15 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 172 (accept_3_3 29 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  172 4 7 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 172 2 13 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 172 (Polychromatic418967fa.accept_16_9_4_12_1_4896 25 52 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 172 4 6 13 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 172 (accept_3_3 23 52 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 172 2 11 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 172 4 5 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 172
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 172 2 9 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 172 (accept_3_3 17 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  172 4 4 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 172 2 7 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 172 4 3 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 172 (accept_3_3 11 52 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 172 2 5 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 172 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 52 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 172 4 2 13 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 172
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 172 2 3 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 172 (accept_3_3 5 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 172
  4 1 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  172 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 172 2 1 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 172)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 172
  (allA_succ_of_accept 50 51 172 (accept_3_3 50 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 172 (accept_3_3 47 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 172
  (Polychromatic418967fa.accept_18_9_15_10_1_395 45 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 172 (accept_3_3 44 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 172 (accept_3_3 41 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 172
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 172 (accept_3_3 38 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 172 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 172 (accept_3_3 35 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 172 (accept_3_3 32 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 172 (accept_3_3 29 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 172 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 172 (accept_3_3 26 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 172 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 172 (accept_3_3 23 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 51 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 172 (accept_3_3 20 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 172 (accept_3_3 17 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 172
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 172 (accept_3_3 14 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 172 (accept_3_3 11 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 172 (Polychromatic418967fa.accept_16_10_3_12_1_1758 10 51 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 172
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 172 (accept_3_3 8 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 172 (accept_3_3 5 51 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 51 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 172 (accept_3_3 2 51 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  172))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 172 (allA_of_3_1 50 50 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 172 (allA_succ_of_accept 48 49 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 172 (accept_3_3 47 49 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 172 (Polychromatic418967fa.accept_12_10_1_4_1_392
  46 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 172 (accept_3_3 44 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 172 (accept_3_3 41 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 172 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 172 (accept_3_3 38 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 172 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 172 (accept_3_3 35 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 172 (accept_3_3 32 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 172 (accept_3_3 29 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 172 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 172 (accept_3_3 26 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 172 (accept_3_3 23 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 172 (accept_3_3 20 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 172 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 172 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 172 (accept_3_3 17 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 172 (accept_3_3 14 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 172 (accept_3_3 11 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 172 (accept_3_3 8 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 172 (accept_3_3 5 49 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 172 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 49 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 172 (accept_3_3 2 49 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 1
  49 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  172))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 172 (allA_succ_of_accept 47 48 172 (accept_3_3 47
  48 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 172 2 23 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 172 4 11 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 172 2 21 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 172 (accept_3_3 41 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 172 4 10 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 172 (Polychromatic418967fa.accept_17_5_14_2_1_4568 39 48 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 172 2 19 24 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 172 4 9 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 172 (accept_3_3 35 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  172 2 17 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 172 4 8 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 172 2 15 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 172 (accept_3_3 29 48 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 172 4 7 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 172 (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 48 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 172 2 13 24 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 172
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 172 4 6 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 172 (accept_3_3 23 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  172 2 11 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 172 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 172 4 5 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 172 2 9 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 172 (accept_3_3 17 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 172 4 4 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 172 2 7 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 172
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 172 4 3 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 172 (accept_3_3 11 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  172 2 5 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 172 4 2 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 172 2 3 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 172 (accept_3_3 5 48 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 172 4 1 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 172 2 1 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 172
  (Polychromatic418967fa.accept_25_1_23_22_1_9719 1 48 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 172)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 172 (allA_of_3_1 47 47 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 172 (allA_succ_of_accept 45 46 172
  (Polychromatic418967fa.accept_19_7_8_1_1_4028 45 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 172 2 22 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 46 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 172 2 21 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 172 (accept_3_3 41 46 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 172 2 20 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 172 (Polychromatic418967fa.accept_15_9_1_7_1_1350 39 46 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 172 2 19 23 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 172
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 172 2 18 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 172 (accept_3_3 35 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  172 2 17 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 172 (Polychromatic418967fa.accept_25_8_21_22_1_9718 33 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 172 2 16 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 46 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 172 2 15 23 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 172 (accept_3_3 29 46 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 172 2 14 23 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 172
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 172 2 13 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 46 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 172 2 12 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 172 (accept_3_3 23 46 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 172 2 11 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 172 2 10 23 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 172 2 9 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 172 (accept_3_3 17 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  172 2 8 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 172 (Polychromatic418967fa.accept_19_15_8_1_1_6794 15 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 172 2 7 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 46 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 172 2 6 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 172 (accept_3_3 11 46 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 172 2 5 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 46 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 172 2 4 23 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 172
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 172 2 3 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 172 (accept_3_3 5 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 172
  2 2 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  172 (Polychromatic418967fa.accept_26_3_20_16_1_9717 3 46 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 46 172 2 1 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 46 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 46 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 172)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  172 (allA_succ_of_accept 44 45 172 (accept_3_3 44 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 172 (accept_3_3 41 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 172 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 172
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 172 (accept_3_3 38 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 172 (accept_3_3 35 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 172
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 172 (accept_3_3 32 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 172 (accept_3_3 29 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 172 (accept_3_3 26 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 172 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 172 (accept_3_3 23 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 172
  (Polychromatic418967fa.accept_14_7_3_4_1_1816 21 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 172 (accept_3_3 20 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 172 (accept_3_3 17 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 172 (Polychromatic418967fa.accept_24_16_21_4_1_9716 16 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 172 (accept_3_3 14 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 172 (Polychromatic418967fa.accept_18_12_9_10_1_3104 12 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 172 (accept_3_3 11 45 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 172 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 45
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 172
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 172 (accept_3_3 8 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 172 (accept_3_3 5 45 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 172 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 45 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 172 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  45 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 172 (accept_3_3 2 45 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  172))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 172 (allA_of_3_1 44 44 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 172 (allA_succ_of_accept 42 43 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 172 (accept_3_3 41 43 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 40
  43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 172 (accept_3_3 38 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 172 (Polychromatic418967fa.accept_19_18_5_1_1_8255 37 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 172 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 172 (accept_3_3 35 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 172 (accept_3_3 32 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 172 (accept_3_3 29 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 172 (Polychromatic418967fa.accept_17_11_9_2_1_8423 28 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 172 (accept_3_3 26 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 172 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 172 (accept_3_3 23 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 172 (accept_3_3 20 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 172 (Polychromatic418967fa.accept_19_18_5_1_1_8255 18 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 172 (accept_3_3 17 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 172 (Polychromatic418967fa.accept_19_16_5_1_1_4019 16 43
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 172 (accept_3_3 14 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 172 (accept_3_3 11 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 172 (accept_3_3 8 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 172 (accept_3_3 5 43 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 172 (accept_3_3 2 43 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 172 (Polychromatic418967fa.accept_10_1_3_2_1_220 1
  43 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  172))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 172 (allA_succ_of_accept 41 42 172 (accept_3_3 41 42 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 172 2 20 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 172 2 19 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 172 (Polychromatic418967fa.accept_16_5_10_12_1_4904 37 42 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 172 2 18 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 172 (accept_3_3 35 42 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 172 2 17 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 172 2 16 21 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 172
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 172 2 15 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 172 (accept_3_3 29 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  172 2 14 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 172 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 172 2 13 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 172 2 12 21 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 172 (accept_3_3 23 42 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 172 2 11 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 172
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 172 2 10 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 172 (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 42 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 172 2 9 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 172 (accept_3_3 17 42 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 172 2 8 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 172 2 7 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 172 2 6 21 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 172 (accept_3_3 11
  42 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 172 2 5 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 172 2 4 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 172 2 3 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 172 (accept_3_3 5 42 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 172 2 2 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 172 2 1 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 172 (Polychromatic418967fa.accept_22_1_20_18_1_8080
  1 42 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  172)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 172 (allA_of_3_1 41 41 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 172 (allA_succ_of_accept 39 40 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 40 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 172 2 19 20 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 172 4 9 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 172 (accept_3_3 35 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40
  172 2 17 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  40 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 40 172 4 8 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 172 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 40 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 172 2 15 20 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 172 (accept_3_3 29 40 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 172 4 7 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 172 2 13 20 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 172 4 6 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 172 (accept_3_3 23 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  172 2 11 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 172 4 5 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 172 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 40 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 172 2 9 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 172 (accept_3_3 17 40 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 172 4 4 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 40 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 172 2 7 20 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 172 4 3 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 172 (accept_3_3 11 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  172 2 5 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 172 4 2 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 172 2 3 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 172 (accept_3_3 5 40 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 172 4 1 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 172 2 1 20 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 172)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 172 (allA_succ_of_accept 38 39 172 (accept_3_3
  38 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 172 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 172 (accept_3_3 35 39 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 172 (accept_3_3 32 39
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 172 (accept_3_3 29 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 172 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 172 (accept_3_3 26 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 172 (accept_3_3 23 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 172 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 172 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 172 (accept_3_3 20 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 172 (accept_3_3 17 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 172 (accept_3_3 14 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 172
  (Polychromatic418967fa.accept_11_1_6_7_1_116 12 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 172 (accept_3_3 11 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 172 (Polychromatic418967fa.accept_22_10_17_18_1_3242 10 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 172 (Polychromatic418967fa.accept_20_9_19_12_1_5221 9 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 172 (accept_3_3 8 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 172 (accept_3_3 5 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 172 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 172 (accept_3_3 2 39 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 172))))))))))))))))))))))))))))))))))))))) (allB_succ 38 172
  (allA_of_3_1 38 38 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 172 (allA_succ_of_accept 36 37 172
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 172 (accept_3_3 35 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 172 (accept_3_3 32 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 172 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 37 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 172
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 172 (accept_3_3 29 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 172 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 172 (accept_3_3 26 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 172
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 172 (accept_3_3 23 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 172 (accept_3_3 20 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 172
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 172 (accept_3_3 17 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 172 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 172 (accept_3_3 14 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 172
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 172 (accept_3_3 11 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 172 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 172 (accept_3_3 8 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 172 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 37 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 172
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 172 (accept_3_3 5 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 37 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 172 (accept_3_3 2 37 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 172))))))))))))))))))))))))))))))))))))) (allB_succ 36 172
  (allA_succ_of_accept 35 36 172 (accept_3_3 35 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  172 2 17 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 172 4 8 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 36 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 172 2 15 18 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 172 (accept_3_3 29 36 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 172 4 7 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 172 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 36 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 172 2 13 18 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 172
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 172 4 6 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 172 (accept_3_3 23 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  172 2 11 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 172 4 5 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 172 2 9 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 172 (accept_3_3 17 36 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 172 4 4 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 36 172 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 36 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 172 2 7 18 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 172
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 172 4 3 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 172 (accept_3_3 11 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  172 2 5 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 172 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 172 4 2 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 172 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 36 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 172 2 3 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 172 (accept_3_3 5 36 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 172 4 1 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 172 2 1 18 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 172
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 172)))))))))))))))))))))))))))))))))))) (allB_succ 35 172 (allA_of_3_1 35 35 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 172 (allA_succ_of_accept 33 34 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 172 2 16 17 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 172 2 15 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 172 (accept_3_3 29 34 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  172 2 14 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 172 2 13 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 34 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 172 2 12 17 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 172 (accept_3_3 23 34 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 172 2 11 17 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 172 2 10 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 172 2 9 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 172 (accept_3_3 17 34 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 172 2 8 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 34 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 172 2 7 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 172 2 6 17 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 172 (accept_3_3 11
  34 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 172 2 5 17 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 172 2 4 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 172 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 172 2 3 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 172 (accept_3_3 5 34 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 172 2 2 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 172 2 1 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  34 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 172))))))))))))))))))))))))))))))))))
  (allB_succ 33 172 (allA_succ_of_accept 32 33 172 (accept_3_3 32 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 172 (accept_3_3 29 33 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 172 (Polychromatic418967fa.accept_19_9_14_1_1_6792
  28 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 172 (accept_3_3 26 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 172 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 172 (accept_3_3 23 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 172
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 172 (accept_3_3 20 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 172 (accept_3_3 17 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 172
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 172 (accept_3_3 14 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 172 (accept_3_3 11 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 172 (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 33 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 172
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 172 (accept_3_3 8 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 172 (accept_3_3 5 33 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 33 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 172 (accept_3_3 2 33 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 172)))))))))))))))))))))))))))))))))
  (allB_succ 32 172 (allA_of_3_1 32 32 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 172
  (allA_succ_of_accept 30 31 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 172 (accept_3_3 29 31 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 172 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 172 (accept_3_3 26 31
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 172 (accept_3_3 23 31 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 172 (accept_3_3 20 31
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 172 (Polychromatic418967fa.accept_8_3_7_4_1_42
  19 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 172
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 172 (accept_3_3 17 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 172 (accept_3_3 14 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 172 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 172
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 172 (accept_3_3 11 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 172 (accept_3_3 8 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 172 (accept_3_3 5 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  172 (Polychromatic418967fa.accept_16_4_15_12_1_1745 4 31 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 172 (accept_3_3 2 31 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 172))))))))))))))))))))))))))))))) (allB_succ 30 172
  (allA_succ_of_accept 29 30 172 (accept_3_3 29 30 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  172 2 14 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 172 2 13 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 30 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 172 2 12 15 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 172 (accept_3_3 23 30 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 172 2 11 15 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 172 2 10 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 172 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 172 2 9 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 172 (accept_3_3 17 30 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 172 2 8 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 172 2 7 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  30 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 172 2 6 15 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 172 (accept_3_3 11
  30 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 172 2 5 15 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 172
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 172 2 4 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 172 2 3 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 172 (accept_3_3 5 30 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 172 2 2 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 172 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 172 2 1 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 172 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1
  30 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 172))))))))))))))))))))))))))))))
  (allB_succ 29 172 (allA_of_3_1 29 29 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 172
  (allA_succ_of_accept 27 28 172 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 28 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 172 2 13 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 25
  28 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 172 4 6 7 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 172 (accept_3_3 23
  28 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 172 2 11 14 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 172
  (Polychromatic418967fa.accept_15_6_13_7_1_222 21 28 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 172 4 5 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 172 (Polychromatic418967fa.accept_21_19_7_4_1_4994 19 28 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 172 2 9 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 172 (accept_3_3 17 28 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 172 4 4 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 172 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 172 2 7 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 172 (Polychromatic418967fa.accept_21_13_7_4_1_4991
  13 28 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 172 4 3 7 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 172 (accept_3_3 11
  28 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 172 2 5 14 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 172
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 28 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 172 4 2 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 172 (Polychromatic418967fa.accept_22_7_6_18_1_9715 7 28 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 172 2 3 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 172 (accept_3_3 5 28 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 172 4 1 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 172 (Polychromatic418967fa.accept_17_3_11_2_1_8435 3 28 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 172 2 1 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 172 (Polychromatic418967fa.accept_11_1_6_7_1_116 1
  28 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 172))))))))))))))))))))))))))))
  (allB_succ 27 172 (allA_succ_of_accept 26 27 172 (accept_3_3 26 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 172 (accept_3_3 23 27 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 172 (Polychromatic418967fa.accept_20_2_7_12_1_5215
  22 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 172
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 172 (accept_3_3 20 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 172 (accept_3_3 17 27 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 172 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 172
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 172 (accept_3_3 14 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 172 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 172 (accept_3_3 11 27 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 172
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 172 (accept_3_3 8 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 172 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 172 (accept_3_3 5 27 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 172 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 172 (accept_3_3 2 27 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 172)))))))))))))))))))))))))))
  (allB_succ 26 172 (allA_of_3_1 26 26 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 172
  (allA_succ_of_accept 24 25 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 172 (accept_3_3 23 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 172 (accept_3_3 20 25
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 172
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 172 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 172 (accept_3_3 17 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 172 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 25 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 172 (accept_3_3 14 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 172 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 172 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 172 (accept_3_3 11 25 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 172 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 25 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 172
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 172 (accept_3_3 8 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  172 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 172 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 172 (accept_3_3 5 25 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 172 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 172 (accept_3_3 2 25 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 172 (Polychromatic418967fa.accept_14_1_11_4_1_3430
  1 25 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 172)))))))))))))))))))))))))
  (allB_succ 24 172 (allA_succ_of_accept 23 24 172 (accept_3_3 23 24 172 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 172 2 11 12 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 172 4 5 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 172 (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 24 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 172 2 9 12 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 172 (accept_3_3 17 24 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 172 4 4 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  24 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 172 2 7 12 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 172
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 172 4 3 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 172 (accept_3_3 11 24 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  172 2 5 12 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 172 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 24 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 172 4 2 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 172 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 172 2 3 12 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 172 (accept_3_3 5 24 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 172 4 1 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 172 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 172 2 1 12 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 172
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 172)))))))))))))))))))))))) (allB_succ 23 172 (allA_of_3_1 23 23 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 172 (allA_succ_of_accept 21 22 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 172 2 10 11 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 172
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 172 2 9 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 172 (accept_3_3 17 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  172 2 8 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 172 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 172 2 7 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 172 2 6 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 172 (accept_3_3 11 22 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 172 2 5 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 172 (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 22 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 172 2 4 11 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 172
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 172 2 3 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 172 (accept_3_3 5 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 172
  2 2 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 172 2 1 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 172 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 22 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 172)))))))))))))))))))))) (allB_succ 21 172 (allA_succ_of_accept 20 21
  172 (accept_3_3 20 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 172 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 172 (accept_3_3 17 21 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 21 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 172 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 172 (accept_3_3 14 21
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 172 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 172
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 172 (accept_3_3 11 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 172 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 172 (accept_3_3 8 21 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 172
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 172 (accept_3_3 5 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  172 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 172 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 172 (accept_3_3 2 21 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 172))))))))))))))))))))) (allB_succ 20 172 (allA_of_3_1 20 20
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 172 (allA_succ_of_accept 18 19 172
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 172 (accept_3_3 17 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 172 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 172 (accept_3_3 14 19 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 172 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 172
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 12 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 172 (accept_3_3 11 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 172 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 172 (accept_3_3 8 19 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 172 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 172
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 172 (accept_3_3 5 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  172 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 19 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 172 (accept_3_3 2 19 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 172))))))))))))))))))) (allB_succ 18 172 (allA_succ_of_accept 17
  18 172 (accept_3_3 17 18 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 172 2 8 9 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 172
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 172 2 7 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 172 (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 18 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 172 2 6 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 172 (accept_3_3 11 18 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 172 2 5 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 172 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 172 2 4 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 172 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7
  18 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 172 2 3 9 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 172 (accept_3_3 5 18
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 172 2 2 9 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 172
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 172 2 1 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 172 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 18 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 172)))))))))))))))))) (allB_succ 17 172 (allA_of_3_1 17 17 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 172 (allA_succ_of_accept 15 16 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 16 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 172 2 7 8 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 172 4 3 4 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 172 (accept_3_3 11 16 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 172 2 5 8 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 172 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 172 4 2 4 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 172 (Polychromatic418967fa.accept_21_7_16_4_1_9713 7
  16 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 172 2 3 8 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 172 (accept_3_3 5 16
  172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 172 4 1 4 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 172
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 16 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 172 2 1 8 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 16 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 172)))))))))))))))) (allB_succ 15 172 (allA_succ_of_accept 14 15 172
  (accept_3_3 14 15 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 172 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 172 (accept_3_3 11 15 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 172 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9
  15 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 172 (accept_3_3 8 15 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 172
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 172 (accept_3_3 5 15 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  172 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 15 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 172 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 172 (accept_3_3 2 15 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 172))))))))))))))) (allB_succ 14 172 (allA_of_3_1 14 14 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 172 (allA_succ_of_accept 12 13 172
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 172 (accept_3_3 11 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 172 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 172 (accept_3_3 8 13 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 172 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 172
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 172 (accept_3_3 5 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  172 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 13 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 172 (accept_3_3 2 13 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 172 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 172 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 172))))))))))))) (allB_succ 12 172
  (allA_succ_of_accept 11 12 172 (accept_3_3 11 12 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  172 2 5 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  172 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 172 4 2 3 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 172 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 172 2 3 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 172 (accept_3_3 5 12 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 172 4 1 3 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 172 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 12 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 172 2 1 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 172 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 172)))))))))))) (allB_succ 11 172
  (allA_of_3_1 11 11 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 172 (allA_succ_of_accept 9 10 172
  (Polychromatic418967fa.accept_19_9_10_1_1_8329 9 10 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 172 2 4 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 172 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 172 2 3 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 172 (accept_3_3 5 10 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 172 2 2 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 172 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 10 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 172 2 1 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 172 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 172)))))))))) (allB_succ 9 172
  (allA_succ_of_accept 8 9 172 (accept_3_3 8 9 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 172
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 172 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 172 (accept_3_3 5 9 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 172 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 9 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 172 (Polychromatic418967fa.accept_16_3_9_12_1_4831 3
  9 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 172 (accept_3_3 2 9 172
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 172))))))))) (allB_succ 8 172
  (allA_of_3_1 8 8 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 172 (allA_succ_of_accept 6 7 172
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 172 (accept_3_3 5 7 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 172
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 172 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 172 (accept_3_3 2 7 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 172 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 7 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 172))))))) (allB_succ 6 172 (allA_succ_of_accept 5 6 172
  (accept_3_3 5 6 172 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 172 2 2 3 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 172
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 172 2 1 3 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 172 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 6 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 172)))))) (allB_succ 5 172 (allA_of_3_1 5 5 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 172 (allA_succ_of_accept 3 4 172 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 172
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 172 2 1 2 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 172
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 4 172 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 172)))) (allB_succ 3 172 (allA_succ_of_accept 2 3 172 (accept_3_3 2 3 172 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 172 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 172))) (allB_succ 2 172 (allA_of_3_1 2 2 172 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


