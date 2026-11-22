-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch199
-- name    : Polychromatic418967fa_Branch199
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:15.263226+00:00
-- url     : https://prove2.me/theorems/3c32bd54-640e-499b-998d-47b66f011309
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch199_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_199 : allB 199 199 :=
  allB_succ' 2 198 199 (Eq.refl Bool.true) (allA_succ_of_accept 1 198 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  198 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 199)) (allB_succ' 3 197 199
  (Eq.refl Bool.true) (allA_of_3_1 3 197 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 196 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 196 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 199 (accept_3_3 2 196 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 199 (Polychromatic418967fa.accept_21_1_7_10_1_2596 1 196 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 199)))) (allB_succ' 5 195 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 195 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 195 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 199 (accept_3_3 2 195 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 199 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  195 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 199))))) (allB_succ' 6 194 199
  (Eq.refl Bool.true) (allA_of_3_1 6 194 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 193 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 193 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 199 (accept_3_3 5 193 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 199 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 193 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 193 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 199 (accept_3_3 2 193 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 199))))))) (allB_succ' 8 192 199 (Eq.refl Bool.true) (allA_succ_of_accept 7 192 199
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 192 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 192 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 199 (accept_3_3 5 192 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 192 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 192 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 199 (Polychromatic418967fa.accept_18_3_12_1_1_3787
  3 192 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 199 (accept_3_3 2
  192 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 199
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 192 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 199)))))))) (allB_succ' 9 191 199 (Eq.refl Bool.true) (allA_of_3_1 9 191 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 190 199 (Eq.refl Bool.true) (allA_succ_of_accept 9 190 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 190 199 (accept_3_3 8 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  190 199 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 190 199 (Polychromatic418967fa.accept_15_6_10_4_1_150 6 190 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 199 (accept_3_3 5 190 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 190 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 190 199 (accept_3_3 2 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  190 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 199)))))))))) (allB_succ' 11 189 199 (Eq.refl Bool.true) (allA_succ_of_accept 10 189 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 189 199 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 189 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 199 (accept_3_3 8 189 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 189 199 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 189 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 199 (accept_3_3 5 189 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 199 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 189 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 199 (accept_3_3 2 189 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 199 (Polychromatic418967fa.accept_25_1_14_24_1_11662 1 189 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 199))))))))))) (allB_succ' 12 188 199
  (Eq.refl Bool.true) (allA_of_3_1 12 188 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 187 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 12 187 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 199 (accept_3_3 11 187 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 199 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 187 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 199 (accept_3_3 8 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 199 (Polychromatic418967fa.accept_19_7_16_9_1_398 7 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 187 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 199 (accept_3_3 5 187 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 187 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 199 (accept_3_3 2 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 199))))))))))))) (allB_succ' 14 186 199 (Eq.refl Bool.true) (allA_succ_of_accept 13 186 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 186 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 186 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 199 (accept_3_3 11 186 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 186 199 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 186 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 186 199 (accept_3_3 8 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  186 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 186 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 186 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 199 (accept_3_3 5 186 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 186 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 186 199 (accept_3_3 2 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  186 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 186 199)))))))))))))) (allB_succ' 15 185 199 (Eq.refl Bool.true) (allA_of_3_1 15 185 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 184 199 (Eq.refl Bool.true) (allA_succ_of_accept 15 184 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 199 (accept_3_3 14 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 184 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 199 (accept_3_3 11 184 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 184 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 199 (accept_3_3 8 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 184 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 199 (accept_3_3 5 184 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 199 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 184 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 199 (accept_3_3 2 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 199)))))))))))))))) (allB_succ' 17 183 199 (Eq.refl Bool.true) (allA_succ_of_accept 16 183
  199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 183 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 199 (accept_3_3 14 183 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 183 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 183 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 199 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 199 (accept_3_3 11
  183 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 199
  (Polychromatic418967fa.accept_6_4_3_1_1_57 10 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 183 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 183 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 199 (accept_3_3 8 183 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 183 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 183 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 6
  183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 199 (accept_3_3 5 183
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 199 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 199
  (Polychromatic418967fa.accept_13_3_1_4_1_945 3 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 199 (accept_3_3 2 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 199 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 183 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 199))))))))))))))))) (allB_succ' 18 182 199 (Eq.refl Bool.true) (allA_of_3_1 18 182 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 181 199 (Eq.refl Bool.true) (allA_succ_of_accept 18 181 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 199 (accept_3_3 17 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 199 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 181 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 199 (accept_3_3 14 181 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 199 (Polychromatic418967fa.accept_17_13_11_12_1_4131 13
  181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 199
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 181 199 (accept_3_3 11 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 181 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 199 (accept_3_3 8 181 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 199 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 181 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 199 (accept_3_3 5 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 199 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 181 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 199 (accept_3_3 2 181 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 199 (Polychromatic418967fa.accept_19_1_10_9_1_10302 1 181 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 199))))))))))))))))))) (allB_succ' 20 180 199
  (Eq.refl Bool.true) (allA_succ_of_accept 19 180 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 180 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 199
  (Polychromatic418967fa.accept_23_18_19_15_1_11661 18 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 180 199 (accept_3_3 17 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 180 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 180 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 180 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 199 (accept_3_3 14 180 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 199
  (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 180 199 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 180 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 199 (accept_3_3 11 180 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 199 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 180 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 180 199 (accept_3_3 8 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  180 199 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 180 199 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 180 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 199 (accept_3_3 5 180 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 199 (Polychromatic418967fa.accept_23_4_19_15_1_11660 4 180 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 199
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 199 (accept_3_3 2 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  180 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 199)))))))))))))))))))) (allB_succ' 21 179 199 (Eq.refl Bool.true) (allA_of_3_1 21 179 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 178 199 (Eq.refl Bool.true) (allA_succ_of_accept 21 178 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 199 (accept_3_3 20 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 199 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 199 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 178 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 199 (accept_3_3 17 178 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 178
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 199 (accept_3_3 14 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 178 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 199 (accept_3_3 11 178 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 199 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 178 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 199 (accept_3_3 8 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 199 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 178 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 199 (accept_3_3 5 178 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 178 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 199 (accept_3_3 2 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 199)))))))))))))))))))))) (allB_succ' 23 177 199 (Eq.refl Bool.true) (allA_succ_of_accept 22
  177 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 199 (accept_3_3 20 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 199 (accept_3_3 17 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 199 (accept_3_3 14 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 199
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 199 (accept_3_3 11 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 199 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 199 (accept_3_3 8 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 177 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 199 (accept_3_3 5 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 199 (accept_3_3 2 177 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 199))))))))))))))))))))))) (allB_succ' 24 176 199
  (Eq.refl Bool.true) (allA_of_3_1 24 176 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 175 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 175 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 199 (accept_3_3 23 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 199 (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 175 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 199 (accept_3_3 20 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 199 (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 199 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 175 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 199 (accept_3_3 17 175 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 199 (accept_3_3 14 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 199 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 199 (accept_3_3 11 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 199 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 175 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 199
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 199 (accept_3_3 8 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 199 (accept_3_3 5 175 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 199 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 175 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 199 (accept_3_3 2 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 199 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 175 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 199))))))))))))))))))))))))) (allB_succ' 26 174 199 (Eq.refl Bool.true) (allA_succ_of_accept
  25 174 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 174 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 199 (accept_3_3 23 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 174 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 174 199 (accept_3_3 20 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 174 199 (Polychromatic418967fa.accept_13_6_5_4_1_3924 19 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 174 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 199 (accept_3_3 17 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 174 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 174 199 (accept_3_3 14 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 174 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 174 199 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 174 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 199 (accept_3_3 11 174 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 199 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 174
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 174 199 (accept_3_3 8 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  174 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 174 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 199 (accept_3_3 5 174 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 174 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 199
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 174 199 (accept_3_3 2 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  174 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 199)))))))))))))))))))))))))) (allB_succ' 27 173 199 (Eq.refl Bool.true) (allA_of_3_1 27 173
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 172 199 (Eq.refl Bool.true) (allA_succ_of_accept 27 172
  199 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 199 (accept_3_3 26 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 199 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 199 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 199 (accept_3_3 23 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 172 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 199 (accept_3_3 20 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 199 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 199 (accept_3_3 17 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 199 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 172
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 199 (accept_3_3 14 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 199 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 199 (accept_3_3 11 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 172
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 199 (accept_3_3 8 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 199 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 172 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 199 (accept_3_3 5 172 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 199 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 172 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 199 (accept_3_3 2 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 199)))))))))))))))))))))))))))) (allB_succ' 29 171 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 171 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 199 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 171
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 199 (accept_3_3 26 171
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 199
  (Polychromatic418967fa.accept_10_5_1_9_1_791 25 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 171 199 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 199 (accept_3_3 23 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 171 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 199 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 199 (accept_3_3 20
  171 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 199
  (Polychromatic418967fa.accept_13_6_2_4_1_923 19 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 171 199 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 199 (accept_3_3 17 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 171 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 199 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 199 (accept_3_3 14
  171 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 199
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 171 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 199 (accept_3_3 11 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 199 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 199 (accept_3_3 8 171
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 199
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 171 199 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 199 (accept_3_3 5 171 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 171 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 199 (Polychromatic418967fa.accept_16_3_11_7_1_770
  3 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 199 (accept_3_3 2
  171 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 199
  (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 171 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 199))))))))))))))))))))))))))))) (allB_succ' 30 170 199 (Eq.refl Bool.true) (allA_of_3_1 30 170 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 169 199 (Eq.refl Bool.true) (allA_succ_of_accept 30 169 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 199 (accept_3_3 29 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 199 (Polychromatic418967fa.accept_17_11_16_12_1_1984 28 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 199 (Polychromatic418967fa.accept_19_8_17_9_1_4542 27 169 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 199 (accept_3_3 26 169 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 199 (Polychromatic418967fa.accept_7_4_1_3_1_277
  25 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 199
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 199 (accept_3_3 23 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 199 (accept_3_3 20 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 199 (accept_3_3 17 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 199 (accept_3_3 14 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 169 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 199
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 199 (accept_3_3 11 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 199 (accept_3_3 8 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 199 (Polychromatic418967fa.accept_19_7_17_9_1_8879 7 169 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 199 (accept_3_3 5 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 199 (accept_3_3 2 169 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 199 (Polychromatic418967fa.accept_17_1_16_12_1_5298 1 169 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 199))))))))))))))))))))))))))))))) (allB_succ' 32
  168 199 (Eq.refl Bool.true) (allA_succ_of_accept 31 168 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 168 199 (accept_3_3 29 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 168 199 (Polychromatic418967fa.accept_13_2_12_4_1_943 28 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 168 199 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 199 (accept_3_3 26 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 168 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 199
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 168 199 (accept_3_3 23 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 168 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 168 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 168 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 199 (accept_3_3 20 168 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 199 (Polychromatic418967fa.accept_25_19_18_24_1_11659 19 168 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 199
  (Polychromatic418967fa.accept_13_5_12_4_1_449 18 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 168 199 (accept_3_3 17 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 168 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 168 199 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 199 (accept_3_3 14 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 168 199 (accept_3_3 11 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 168 199 (Polychromatic418967fa.accept_19_10_16_9_1_10157 10 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 199 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 199 (accept_3_3 8 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 199
  (Polychromatic418967fa.accept_19_6_16_9_1_10184 6 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 168 199 (accept_3_3 5 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  168 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 168 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 168 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 199 (accept_3_3 2 168 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 199 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 168 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 199)))))))))))))))))))))))))))))))) (allB_succ' 33
  167 199 (Eq.refl Bool.true) (allA_of_3_1 33 167 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 166 199
  (Eq.refl Bool.true) (allA_succ_of_accept 33 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 199 (accept_3_3 32 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 199 (Polychromatic418967fa.accept_13_5_10_4_1_1564 31 166
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 199 (accept_3_3 29 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 199 (accept_3_3 26 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 199 (accept_3_3 23 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 199 (accept_3_3 20 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 199 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 199
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 199 (accept_3_3 17 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 199 (accept_3_3 14 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 199 (accept_3_3 11 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 199 (Polychromatic418967fa.accept_20_10_6_19_1_5691 10 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 199 (accept_3_3 8 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 199 (accept_3_3 5 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 166 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 199 (accept_3_3 2 166 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 199)))))))))))))))))))))))))))))))))) (allB_succ' 35
  165 199 (Eq.refl Bool.true) (allA_succ_of_accept 34 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 199 (accept_3_3 32 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 199 (accept_3_3 29 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 199
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 199 (accept_3_3 26 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 199 (accept_3_3 23 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 199
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 199 (accept_3_3 20 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 199 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 199 (accept_3_3 17 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 199
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 199 (accept_3_3 14 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 199 (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 199 (accept_3_3 11 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 199
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 199 (accept_3_3 8 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 199 (accept_3_3 5 165 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 199
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 199 (accept_3_3 2 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 199))))))))))))))))))))))))))))))))))) (allB_succ' 36 164 199 (Eq.refl Bool.true)
  (allA_of_3_1 36 164 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 163 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 163 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 199 (accept_3_3 35 163 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 163 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 199 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 199 (accept_3_3 32
  163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 199
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 163 199 (Polychromatic418967fa.accept_20_10_3_19_1_2931 30 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 199 (accept_3_3 29 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 199
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 199 (accept_3_3 26 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 199 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 199 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 199 (accept_3_3 23 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 199
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 199 (accept_3_3 20 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 199 (Polychromatic418967fa.accept_27_18_1_10_1_11658 18 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 199 (accept_3_3 17 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 199 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 163
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 199
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 199 (accept_3_3 14 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 199 (accept_3_3 11 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 199 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 163 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 199
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 199 (accept_3_3 8 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 199 (Polychromatic418967fa.accept_19_7_11_9_1_2139 7 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 199 (accept_3_3 5 163 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 163 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 199
  (Polychromatic418967fa.accept_13_3_7_4_1_435 3 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 199 (accept_3_3 2 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 199))))))))))))))))))))))))))))))))))))) (allB_succ' 38 162 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 199 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 162
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 162 199 (accept_3_3 35 162
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 199
  (Polychromatic418967fa.accept_19_15_10_9_1_5956 34 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 199 (accept_3_3 32 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 199 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 199
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 199 (accept_3_3 29 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 199 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 199 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 199 (accept_3_3 26 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 199
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 199 (accept_3_3 23 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 199 (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 199 (accept_3_3 20 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 199
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 199 (accept_3_3 17 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 199 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 199 (accept_3_3 14 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 199
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 199 (accept_3_3 11 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 199 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 199 (accept_3_3 8 162 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 199 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 199
  (Polychromatic418967fa.accept_19_6_10_9_1_10215 6 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 199 (accept_3_3 5 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 199 (Polychromatic418967fa.accept_19_3_10_9_1_7338 3 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 199 (accept_3_3 2 162 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 199))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 161 199 (Eq.refl Bool.true) (allA_of_3_1 39 161 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 160 199 (Eq.refl Bool.true) (allA_succ_of_accept 39 160 199 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 199 (accept_3_3 38
  160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 160 199 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 160 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 199 (accept_3_3 35 160 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 160 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 160 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 160 199 (accept_3_3 32 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 160 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 160 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 160 199 (accept_3_3 29 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 199 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 160 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 199 (accept_3_3 26 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 160 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 160 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 199 (accept_3_3 23 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 160 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 160 199 (accept_3_3 20 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 160 199 (Polychromatic418967fa.accept_17_2_7_12_1_1078 19 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 160 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 199 (accept_3_3 17 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 160 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 160 199 (accept_3_3 14 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 199 (accept_3_3 11 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 160 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 199 (accept_3_3 8 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 199 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 199 (accept_3_3 5 160 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 199 (accept_3_3 2 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 199 (Polychromatic418967fa.accept_19_1_8_9_1_3304 1 160 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 199)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 159 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 159 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 199 (accept_3_3 38 159 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 199
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 199 (accept_3_3 35 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 199 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 199 (accept_3_3 32 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 159 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 199 (accept_3_3 29 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 199 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 199 (accept_3_3 26 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 159 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 199
  (Polychromatic418967fa.accept_16_8_15_7_1_5658 24 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 199 (accept_3_3 23 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 199 (accept_3_3 20 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 199 (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 159 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 199
  (Polychromatic418967fa.accept_17_1_6_12_1_1944 18 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 199 (accept_3_3 17 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 199 (accept_3_3 14 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 199 (accept_3_3 11 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 199 (accept_3_3 8 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 199
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 199 (accept_3_3 5 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 199 (accept_3_3 2 159 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 199)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 158 199 (Eq.refl Bool.true) (allA_of_3_1 42 158 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 157 199 (Eq.refl Bool.true) (allA_succ_of_accept 42 157 199 (Polychromatic418967fa.accept_4_2_1_3_1_27
  42 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 199 (accept_3_3 41
  157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 199
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 157 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 157 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 199 (accept_3_3 38 157 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 157 199 (Polychromatic418967fa.accept_19_18_5_9_1_1112 37 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 199
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 199 (accept_3_3 35 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 199 (accept_3_3 32 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 199 (Polychromatic418967fa.accept_13_5_1_4_1_3966 31 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 199 (accept_3_3 29 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 199 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 199 (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 199 (accept_3_3 26 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 157 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 199 (accept_3_3 23 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 199 (accept_3_3 20 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 199 (Polychromatic418967fa.accept_17_2_4_12_1_6587 19 157 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 199 (accept_3_3 17 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 199 (accept_3_3 14 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 199 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 199 (accept_3_3 11 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 199 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 199 (accept_3_3 8 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 199 (accept_3_3 5 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 199 (Polychromatic418967fa.accept_16_4_13_7_1_4522 4 157 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 199 (accept_3_3 2 157 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 199 (Polychromatic418967fa.accept_19_1_5_9_1_10341 1 157 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 199)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 156 199 (Eq.refl Bool.true) (allA_succ_of_accept 43 156 199 (Polychromatic418967fa.accept_7_1_2_3_1_257
  43 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 199 (accept_3_3 41 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 199 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 199 (accept_3_3 38 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 199 (Polychromatic418967fa.accept_16_5_12_7_1_3411 37 156
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 199
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 199 (accept_3_3 35 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 199 (accept_3_3 32 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 199
  (Polychromatic418967fa.accept_20_10_16_19_1_5674 30 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 199 (accept_3_3 29 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 199 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 156 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 199 (accept_3_3 26 156 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 199 (Polychromatic418967fa.accept_9_7_3_1_1_386
  25 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 199 (accept_3_3 23 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 199 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 199 (accept_3_3 20 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 199
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 199 (accept_3_3 17 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 199 (accept_3_3 14 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 199
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 199 (accept_3_3 11 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 199 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 199 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 199 (accept_3_3 8 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 199
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 199 (accept_3_3 5 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 156 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 199 (accept_3_3 2 156 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 199))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 155 199 (Eq.refl Bool.true) (allA_of_3_1 45 155 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 154 199 (Eq.refl Bool.true) (allA_succ_of_accept 45 154 199 (Polychromatic418967fa.accept_4_1_2_3_1_9
  45 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 199 (accept_3_3 44
  154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 199
  (Polychromatic418967fa.accept_10_3_4_9_1_15 43 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 154 199 (Polychromatic418967fa.accept_19_4_2_9_1_4584 42 154 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 199 (accept_3_3 41 154 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 154 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 199 (accept_3_3 38 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 199 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 199 (accept_3_3 35 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 199 (Polychromatic418967fa.accept_13_8_11_4_1_1553 34 154
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 199 (accept_3_3 32 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 199 (Polychromatic418967fa.accept_18_13_10_1_1_9025 31 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 199 (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 199 (accept_3_3 29 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 199 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 154
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 199 (accept_3_3 26 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 199 (Polychromatic418967fa.accept_20_4_14_19_1_4222 24 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 199 (accept_3_3 23 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 199 (Polychromatic418967fa.accept_21_1_7_10_1_2596 22 154
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 199 (accept_3_3 20 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 199 (Polychromatic418967fa.accept_13_6_11_4_1_938 19 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 199 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 199 (accept_3_3 17 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 154
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 199 (accept_3_3 14 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 199 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 199 (accept_3_3 11 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 199 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 154
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 199
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 199 (accept_3_3 8 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 199 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 199 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 154 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 199 (accept_3_3 5 154 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 154 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 199 (accept_3_3 2 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 199)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 153 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 199 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 153
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 199 (accept_3_3 44 153
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 199
  (Polychromatic418967fa.accept_19_5_1_9_1_8895 43 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 199 (accept_3_3 41 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 153 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 199 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 199 (accept_3_3 38
  153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 199 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 199 (accept_3_3 35 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 199 (Polychromatic418967fa.accept_13_7_10_4_1_919
  33 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 199 (accept_3_3 32
  153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 199
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 199 (accept_3_3 29 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 153 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 199 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 199 (accept_3_3 26
  153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 199
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 153 199 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 199 (accept_3_3 23 153 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 199
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 199 (accept_3_3 20 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 199 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 199 (accept_3_3 17 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 199
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 199 (accept_3_3 14 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 199 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 199 (Polychromatic418967fa.accept_19_12_1_9_1_10281 12 153 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 199 (accept_3_3 11 153 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 199 (accept_3_3 8 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 199 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 199 (accept_3_3 5 153 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 199
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 199 (accept_3_3 2 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 199 (Polychromatic418967fa.accept_13_1_10_4_1_954 1 153 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 199))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 152 199 (Eq.refl
  Bool.true) (allA_of_3_1 48 152 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 151 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 151 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 199 (accept_3_3 47 151 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 151 199 (Polychromatic418967fa.accept_19_8_18_9_1_10160 46 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 199
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 199 (accept_3_3 44 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 199 (accept_3_3 41 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 199 (accept_3_3 38 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 199 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 199 (accept_3_3 35 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 199
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 199 (accept_3_3 32 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 199 (accept_3_3 29 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 199 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 199
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 199 (accept_3_3 26 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 199 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 199 (accept_3_3 23 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 199 (accept_3_3 20 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 199 (Polychromatic418967fa.accept_21_19_4_10_1_3914 19 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 199 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 199 (accept_3_3 17 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 199 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 151
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 199
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 199 (accept_3_3 14 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 199 (accept_3_3 11 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 199 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 151 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 199
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 199 (accept_3_3 8 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 199 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 199 (accept_3_3 5 151 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 199 (accept_3_3 2 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 199))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 150 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 48
  150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 199 (accept_3_3 47
  150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 199
  (Polychromatic418967fa.accept_19_8_17_9_1_4542 46 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 199 (accept_3_3 44 150 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 150 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 199 (Polychromatic418967fa.accept_13_3_7_4_1_435
  42 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 199 (accept_3_3 41
  150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 199
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 150 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 150 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 199 (accept_3_3 38 150 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 199
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 199 (accept_3_3 35 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 199 (accept_3_3 32 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 199 (accept_3_3 29 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 199 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 199 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 199 (accept_3_3 26 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 199
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 199 (accept_3_3 23 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 199 (accept_3_3 20 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 199 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 199
  (Polychromatic418967fa.accept_21_18_3_10_1_8534 18 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 199 (accept_3_3 17 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 150 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 199 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 150
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 199 (accept_3_3 14 150
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 199 (accept_3_3 11 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 199 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 199 (accept_3_3 8 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 199
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 199 (accept_3_3 5 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 150 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 199 (accept_3_3 2 150 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  199)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 149 199 (Eq.refl Bool.true) (allA_of_3_1 51 149
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 148 199 (Eq.refl Bool.true) (allA_succ_of_accept 51 148
  199 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 148 199 (accept_3_3 50 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 148 199 (Polychromatic418967fa.accept_13_10_5_4_1_3107 49 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 148 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 148 199 (accept_3_3 47 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 148 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 148 199 (accept_3_3 44 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 148 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 148 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 199 (accept_3_3 41 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 148 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 148 199 (accept_3_3 38 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 148 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 148 199 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 199 (accept_3_3 35 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 148 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 148 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 199 (accept_3_3 32 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 199 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 199 (accept_3_3 29 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 199 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 199 (accept_3_3 26 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 199 (accept_3_3 23 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 199 (accept_3_3 20 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 199 (accept_3_3 17 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 199 (accept_3_3 14 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 199 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 199 (accept_3_3 11 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 199 (accept_3_3 8 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 199 (accept_3_3 5 148 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 199
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 199 (accept_3_3 2 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 199 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 148 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 199)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 147 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 199 (Polychromatic418967fa.accept_9_6_3_1_1_155
  51 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 199 (accept_3_3 50
  147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 199
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 147 199 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 147 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 199 (accept_3_3 47 147 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 199 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 199 (accept_3_3 44
  147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 199
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 147 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 147 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 199 (accept_3_3 41 147 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 199
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 199 (accept_3_3 38 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 199 (Polychromatic418967fa.accept_15_7_12_4_1_1236 37 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 199 (accept_3_3 35 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 199 (accept_3_3 32 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 199 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 199 (accept_3_3 29 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 199
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 199 (accept_3_3 26 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 199 (accept_3_3 23 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 199
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 199 (accept_3_3 20 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 199 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 199 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 199 (accept_3_3 17 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 199 (accept_3_3 14 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 199 (accept_3_3 11 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 199
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 199 (accept_3_3 8 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 199 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 199 (accept_3_3 5 147 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 199
  (Polychromatic418967fa.accept_19_3_14_9_1_8866 3 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 199 (accept_3_3 2 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 199 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 147 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 199))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 146 199 (Eq.refl
  Bool.true) (allA_of_3_1 54 146 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 145 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 199 (accept_3_3 53 145 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 145 199 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 199 (accept_3_3 50 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 199 (Polychromatic418967fa.accept_21_7_19_10_1_8567 49 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 199 (Polychromatic418967fa.accept_17_14_9_12_1_5350 48 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 199 (accept_3_3 47 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 199
  (Polychromatic418967fa.accept_13_6_2_4_1_923 45 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 199 (accept_3_3 44 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 199 (accept_3_3 41 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 199 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 145 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 199
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 199 (accept_3_3 38 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 199 (accept_3_3 35 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 199
  (Polychromatic418967fa.accept_19_14_12_9_1_4587 33 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 145 199 (accept_3_3 32 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 145 199 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 145 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 199 (accept_3_3 29 145 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 199
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 199 (Polychromatic418967fa.accept_32_27_17_7_1_11657 27 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 199 (accept_3_3 26 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 199 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 145
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 199
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 199 (accept_3_3 23 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 199 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 199 (accept_3_3 20 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 199 (Polychromatic418967fa.accept_13_6_2_4_1_923 19 145
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 199 (accept_3_3 17 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 199 (accept_3_3 14 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 199 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 145 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 199
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 199 (accept_3_3 11 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 199 (accept_3_3 8 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 199 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 199 (accept_3_3 5 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 199 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 145 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 199 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 199 (accept_3_3 2 145 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  199))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 144 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 144 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 199 (Polychromatic418967fa.accept_17_3_8_12_1_6573 54 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 199 (accept_3_3 53 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 199
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 52 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 144 199 (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 199 (accept_3_3 50 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 199 (Polychromatic418967fa.accept_13_10_1_4_1_3103 49 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 199
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 144 199 (accept_3_3 47 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 144 199 (Polychromatic418967fa.accept_19_8_11_9_1_8827 46 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 199 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 199 (accept_3_3 44 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 199
  (Polychromatic418967fa.accept_13_3_1_4_1_945 42 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 199 (accept_3_3 41 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 144 199 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 199 (Polychromatic418967fa.accept_17_5_8_12_1_6609 39 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 199 (accept_3_3 38 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 199 (Polychromatic418967fa.accept_17_3_8_12_1_6573 37 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 199
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 199 (accept_3_3 35 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 199 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 144 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 199 (accept_3_3 32 144 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 199 (Polychromatic418967fa.accept_13_5_1_4_1_3966 31 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 199
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 30 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 199 (accept_3_3 29 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 199 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 144 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 199 (accept_3_3 26 144 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 199 (Polychromatic418967fa.accept_10_5_4_9_1_420
  25 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 199
  (Polychromatic418967fa.accept_21_3_18_10_1_10020 24 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 199 (accept_3_3 23 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 144 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 199 (Polychromatic418967fa.accept_14_7_4_3_1_488 21 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 199 (accept_3_3 20 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 199
  (Polychromatic418967fa.accept_22_19_12_1_1_11606 19 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 199 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 199 (accept_3_3 17 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 199 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 199
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 199 (accept_3_3 14 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 199 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 199 (accept_3_3 11 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 199 (Polychromatic418967fa.accept_13_10_1_4_1_3103 10 144
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 199
  (Polychromatic418967fa.accept_20_9_4_19_1_10052 9 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 199 (accept_3_3 8 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 199 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 199 (accept_3_3 5 144 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 199 (Polychromatic418967fa.accept_17_4_8_12_1_9165 4 144 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 199
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 199 (accept_3_3 2 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 199)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 143 199 (Eq.refl
  Bool.true) (allA_of_3_1 57 143 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 142 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 199 (accept_3_3 56 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 142 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 199 (Polychromatic418967fa.accept_7_5_2_3_1_106
  54 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 142 199 (accept_3_3 53
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 142 199
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 142 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 199 (accept_3_3 50 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 199 (Polychromatic418967fa.accept_7_6_2_3_1_107
  48 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 142 199 (accept_3_3 47
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 199
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 199 (accept_3_3 44 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 142 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 199 (Polychromatic418967fa.accept_9_6_7_1_1_145
  42 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 199 (accept_3_3 41
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 199
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 142 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 199 (accept_3_3 38 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 199 (Polychromatic418967fa.accept_7_1_2_3_1_257
  36 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 199 (accept_3_3 35
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 142 199
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 199 (accept_3_3 32 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 142 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 199 (Polychromatic418967fa.accept_9_3_7_1_1_143
  30 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 199 (accept_3_3 29
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 199
  (Polychromatic418967fa.accept_12_4_10_7_1_149 28 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 142 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 199 (accept_3_3 26 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 199 (Polychromatic418967fa.accept_9_6_7_1_1_145
  24 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 199 (accept_3_3 23
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 199
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 199 (accept_3_3 20 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 142 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 199 (Polychromatic418967fa.accept_13_5_12_4_1_449
  18 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 199 (accept_3_3 17
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 199
  (Polychromatic418967fa.accept_12_4_10_7_1_149 16 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 142 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 199 (accept_3_3 14 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 199 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 199 (accept_3_3 11
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 199
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 199 (accept_3_3 8 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 142 199 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 199 (accept_3_3 5 142
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 199
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 142 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 142 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 199 (accept_3_3 2 142 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 142 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 141 199 (Eq.refl Bool.true) (allA_succ_of_accept 58 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27
  58 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 199 (accept_3_3 56 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 141 199 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 199 (accept_3_3 53 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 199
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 199 (accept_3_3 50 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 141 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 199 (accept_3_3 47 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 199
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 199 (accept_3_3 44 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 199 (accept_3_3 41 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 199
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 199 (accept_3_3 38 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 199 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 199 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 199 (accept_3_3 35 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 199
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 199 (accept_3_3 32 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 199 (accept_3_3 29 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 199
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 199 (accept_3_3 26 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 199 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 199 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 199 (accept_3_3 23 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 199 (accept_3_3 20 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 199 (accept_3_3 17 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 199
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 199 (accept_3_3 14 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 199 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 199 (accept_3_3 11 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 199
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 199 (accept_3_3 8 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 199 (accept_3_3 5 141 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 199 (accept_3_3 2 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 199 (Polychromatic418967fa.accept_19_1_8_9_1_3304 1 141 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 140 199
  (Eq.refl Bool.true) (allA_of_3_1 60 140 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 139 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 139 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 199 (accept_3_3 59 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 199 (accept_3_3 56 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 199 (Polychromatic418967fa.accept_19_17_6_9_1_8856 55 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 199 (Polychromatic418967fa.accept_19_16_6_9_1_7335 54 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 199 (accept_3_3 53 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 139 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 199 (accept_3_3 50 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 199 (Polychromatic418967fa.accept_17_15_3_12_1_9179 49 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 199 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 199 (accept_3_3 47 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 199
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 199 (accept_3_3 44 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 199 (accept_3_3 41 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 199 (Polychromatic418967fa.accept_22_18_7_1_1_11656 40 139 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 199
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 199 (accept_3_3 38 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 199 (accept_3_3 35 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 199 (accept_3_3 32 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 199 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 199 (accept_3_3 29 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 199
  (Polychromatic418967fa.accept_24_3_19_7_1_11602 27 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 139 199 (accept_3_3 26 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 139 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 199 (accept_3_3 23 139 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 199 (Polychromatic418967fa.accept_19_3_6_9_1_7334
  22 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 199 (accept_3_3 20 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 199 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 199 (accept_3_3 17 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 199 (accept_3_3 14 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 199 (Polychromatic418967fa.accept_19_13_6_9_1_5989 13 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 199 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 199 (accept_3_3 11 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 199 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 139 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 199 (accept_3_3 8 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 199 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 199 (accept_3_3 5 139 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 199 (accept_3_3 2 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 199 (Polychromatic418967fa.accept_21_1_13_10_1_11627 1 139 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 138 199
  (Eq.refl Bool.true) (allA_succ_of_accept 61 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 199 (accept_3_3 59 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 199 (accept_3_3 56 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 199 (Polychromatic418967fa.accept_17_4_2_12_1_6554 55 138 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 199
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 199 (accept_3_3 53 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 199 (accept_3_3 50 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 199
  (Polychromatic418967fa.accept_13_9_8_4_1_937 48 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 138 199 (accept_3_3 47 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 138 199 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 199 (accept_3_3 44 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 199 (accept_3_3 41 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 199 (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 199 (accept_3_3 38 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 199
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 199 (accept_3_3 35 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 199 (accept_3_3 32 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 199
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 199 (accept_3_3 29 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 199 (Polychromatic418967fa.accept_25_3_13_24_1_11655 28 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 199 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 199 (accept_3_3 26 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 199 (accept_3_3 23 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 199 (accept_3_3 20 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 199 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 138 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 199
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 199 (accept_3_3 17 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 199 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 199 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 199 (accept_3_3 14 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 199
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 138 199 (accept_3_3 11 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 138 199 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 199 (accept_3_3 8 138 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 199 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 199
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 199 (accept_3_3 5 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 199 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 138 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 199 (Polychromatic418967fa.accept_16_3_10_7_1_4518 3 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 199 (accept_3_3 2 138 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  199)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 137 199 (Eq.refl Bool.true)
  (allA_of_3_1 63 137 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 136 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 199 (accept_3_3 62 136 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 136 199 (Polychromatic418967fa.accept_13_9_6_4_1_2243 61 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 199
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 60 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 199 (accept_3_3 59 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 199 (accept_3_3 56 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 199 (Polychromatic418967fa.accept_10_5_6_9_1_2235 55 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 199
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 199 (accept_3_3 53 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 199 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 199 (accept_3_3 50 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 199 (Polychromatic418967fa.accept_13_10_6_4_1_1583 49 136 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 199
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 199 (accept_3_3 47 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 199 (accept_3_3 44 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 199 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 199
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 199 (accept_3_3 41 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 199 (Polychromatic418967fa.accept_23_17_21_15_1_11654 40 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 199 (accept_3_3 38 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 199 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 136
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 199
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 199 (accept_3_3 35 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 199 (accept_3_3 32 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 199 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 199
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 199 (accept_3_3 29 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 199 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 199 (accept_3_3 26 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 199 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 199
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 199 (accept_3_3 23 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 199 (accept_3_3 20 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 199 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 199
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 199 (accept_3_3 17 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 199 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 199 (accept_3_3 14 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 199 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 199
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 199 (accept_3_3 11 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 199 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 199 (accept_3_3 8 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 199 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 199
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 199 (accept_3_3 5 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 199 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 136 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 199 (accept_3_3 2 136 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 199 (Polychromatic418967fa.accept_16_1_8_7_1_3377 1 136 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  199)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 135 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 199 (Polychromatic418967fa.accept_23_17_20_15_1_11653 63
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 199 (accept_3_3 62
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 199
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 135 199 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 199 (accept_3_3 59 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 199 (Polychromatic418967fa.accept_7_1_2_3_1_257
  57 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 199 (accept_3_3 56
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 199
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 135 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 199 (accept_3_3 53 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 199 (Polychromatic418967fa.accept_10_1_5_9_1_157
  51 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 199 (accept_3_3 50
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 199
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 49 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 135 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 199 (accept_3_3 47 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 199 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 199 (accept_3_3 44
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 199
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 135 199 (Polychromatic418967fa.accept_18_6_9_1_1_3769 42 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 199 (accept_3_3 41 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 199 (Polychromatic418967fa.accept_18_3_9_1_1_3690
  39 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 199 (accept_3_3 38
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 199
  (Polychromatic418967fa.accept_19_18_2_9_1_8870 37 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 135 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 199 (accept_3_3 35 135 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 199 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 199 (accept_3_3 32
  135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 199
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 135 199 (Polychromatic418967fa.accept_17_13_16_12_1_6562 30 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 199 (accept_3_3 29 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 199
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 199 (accept_3_3 26 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 199 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 199 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 199 (accept_3_3 23 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 199
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 199 (accept_3_3 20 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 199 (Polychromatic418967fa.accept_17_1_16_12_1_5298 18 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 199 (accept_3_3 17 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 199
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 199 (accept_3_3 14 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 199 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 199 (accept_3_3 11 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 199
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 199 (accept_3_3 8 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 199 (Polychromatic418967fa.accept_19_7_2_9_1_6006 7 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 199 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 199 (accept_3_3 5 135 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 199 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 199
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 3 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 199 (accept_3_3 2 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 199 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 134 199
  (Eq.refl Bool.true) (allA_of_3_1 66 134 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 133 199 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 133 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 199 (accept_3_3 65 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 199 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 199
  (Polychromatic418967fa.accept_24_15_13_7_1_11652 63 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 133 199 (accept_3_3 62 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 133 199 (Polychromatic418967fa.accept_21_19_7_10_1_7006 61 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 199 (Polychromatic418967fa.accept_9_6_7_1_1_145
  60 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 199 (accept_3_3 59
  133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 133 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 133 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 199 (accept_3_3 56 133 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 133 199 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 199 (accept_3_3 53 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 199 (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 199 (accept_3_3 50 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 199 (accept_3_3 47 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 199 (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 199 (accept_3_3 44 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 199 (Polychromatic418967fa.accept_16_11_5_7_1_2395 43 133
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 199 (accept_3_3 41 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 199 (accept_3_3 38 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 199 (Polychromatic418967fa.accept_21_16_7_10_1_8601 37 133 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 199
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 199 (accept_3_3 35 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 199 (accept_3_3 32 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 199 (accept_3_3 29 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 199 (Polychromatic418967fa.accept_16_12_5_7_1_2360 28 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 199 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 199 (accept_3_3 26 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 199 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 133
  199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 199
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 199 (accept_3_3 23 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 199 (accept_3_3 20 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 199 (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 133 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 199 (accept_3_3 17 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 199 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 199 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 199 (accept_3_3 14 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 199
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 199 (accept_3_3 11 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 199 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 199 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 199 (accept_3_3 8 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 199 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 133 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 199
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 199 (accept_3_3 5 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 199 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 199 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 199 (accept_3_3 2 133 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 199 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 133 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 132 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 199 (accept_3_3 65 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 199
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 64 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 132 199 (Polychromatic418967fa.accept_13_11_2_4_1_1590 63 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 199 (accept_3_3 62 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 132 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271
  60 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 199 (accept_3_3 59
  132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 199
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 132 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 199 (accept_3_3 56 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 132 199 (Polychromatic418967fa.accept_23_9_17_15_1_9916 55 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 199
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 132 199 (accept_3_3 53 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 132 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 132 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 199 (accept_3_3 50 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 199 (accept_3_3 47 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 199 (Polychromatic418967fa.accept_13_6_2_4_1_923 45 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 199 (accept_3_3 44 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 199
  (Polychromatic418967fa.accept_20_2_12_19_1_11651 42 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 199 (accept_3_3 41 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 132 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 199 (accept_3_3 38 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 199 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 199
  (Polychromatic418967fa.accept_21_15_6_10_1_10016 36 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 199 (accept_3_3 35 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 199 (Polychromatic418967fa.accept_17_16_13_12_1_4092 33
  132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 199 (accept_3_3 32
  132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 199
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 132 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 199 (accept_3_3 29 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 132 199 (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 199
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 132 199 (accept_3_3 26 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 132 199 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 199 (accept_3_3 23 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 199
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 199 (accept_3_3 20 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 132 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 132 199 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 199 (accept_3_3 17 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 199
  (Polychromatic418967fa.accept_19_15_18_9_1_8869 15 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 132 199 (accept_3_3 14 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 199 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 199 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 199 (accept_3_3 11 132 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 199
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 132 199 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 199 (accept_3_3 8 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 132 199 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 199 (Polychromatic418967fa.accept_13_6_2_4_1_923 6
  132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 199 (accept_3_3 5 132
  199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 199
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 132 199 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 199 (accept_3_3 2 132 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 132 199 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 132 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  199)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 131 199 (Eq.refl Bool.true)
  (allA_of_3_1 69 131 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 130 199 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 199 (accept_3_3 68 130 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 130 199 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 130 199 (accept_3_3 65 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 130 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 199 (accept_3_3 62 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 130 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 130 199 (accept_3_3 59 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 130 199 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 199 (accept_3_3 56 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 130 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 130 199
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 199 (accept_3_3 53 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 130 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 130 199 (accept_3_3 50 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 199
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 199 (accept_3_3 47 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 199 (Polychromatic418967fa.accept_19_8_16_9_1_8847 46 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 199 (accept_3_3 44 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 199 (accept_3_3 41 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 199 (accept_3_3 38 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 199
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 130 199 (accept_3_3 35 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 130 199 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 199 (accept_3_3 32 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 199 (Polychromatic418967fa.accept_17_14_11_12_1_4109 31 130 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 199 (accept_3_3 29 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 199 (accept_3_3 26 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 199
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 199 (accept_3_3 23 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 199 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 199 (accept_3_3 20 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 199 (Polychromatic418967fa.accept_21_19_4_10_1_3914 19 130 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 199
  (Polychromatic418967fa.accept_19_18_16_9_1_4556 18 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 130 199 (accept_3_3 17 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 130 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 130 199 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 199
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 199 (accept_3_3 14 130 199
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 199
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 199 (accept_3_3 11 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 199 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 199 (accept_3_3 8 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 199 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 199
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 199 (accept_3_3 5 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 199 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 199 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 199 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 199 (accept_3_3 2 130 199 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 199 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 199 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  199))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_199_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


